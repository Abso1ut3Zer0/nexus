use std::collections::HashSet;
use std::fmt::Write;

use super::{EmitError, HEADER, RField, emit_value_accessor, snake};

/// Tag numbers that are always scanned by the header decoder regardless of
/// what the dictionary's `<header>` section declares.  These are protocol-
/// mandatory for session-layer operation.
const SESSION_TAGS: &[u32] = &[
    8,  // BeginString
    9,  // BodyLength
    35, // MsgType
    34, // MsgSeqNum
    49, // SenderCompID
    56, // TargetCompID
    43, // PossDupFlag
    52, // SendingTime
];

pub fn emit(header_fields: &[RField]) -> Result<String, EmitError> {
    let mut s = String::new();
    s.push_str(HEADER);

    let synth_fields = build_synth_session_fields(header_fields);
    let mut ordered: Vec<&RField> = Vec::new();
    let mut seen: HashSet<u32> = HashSet::new();

    // Session fields first (stable order from SESSION_TAGS).
    for &tag in SESSION_TAGS {
        if !seen.insert(tag) {
            continue;
        }
        if let Some(f) = header_fields.iter().find(|f| f.number == tag) {
            ordered.push(f);
        } else if let Some(f) = synth_fields.iter().find(|f| f.number == tag) {
            ordered.push(f);
        }
    }
    // Dictionary-specific header fields after session fields.
    for f in header_fields {
        if seen.insert(f.number) {
            ordered.push(f);
        }
    }

    emit_struct(&mut s, &ordered);
    emit_decode(&mut s, &ordered);
    emit_fix_header_impl(&mut s, &ordered)?;
    emit_msg_type_accessor(&mut s);
    emit_accessors(&mut s, &ordered);

    Ok(s)
}

/// Synthesise RField entries for session tags that the dictionary didn't declare.
fn build_synth_session_fields(dict_fields: &[RField]) -> Vec<RField> {
    let dict_tags: HashSet<u32> = dict_fields.iter().map(|f| f.number).collect();
    let mut out = Vec::new();
    let synths: &[(u32, &str, crate::dict::FieldType)] = &[
        (8, "BeginString", crate::dict::FieldType::String),
        (9, "BodyLength", crate::dict::FieldType::Length),
        (35, "MsgType", crate::dict::FieldType::String),
        (34, "MsgSeqNum", crate::dict::FieldType::SeqNum),
        (49, "SenderCompID", crate::dict::FieldType::String),
        (56, "TargetCompID", crate::dict::FieldType::String),
        (43, "PossDupFlag", crate::dict::FieldType::Bool),
        (52, "SendingTime", crate::dict::FieldType::Timestamp),
    ];
    for &(tag, name, ftype) in synths {
        if !dict_tags.contains(&tag) {
            out.push(RField {
                name: name.to_string(),
                number: tag,
                ftype,
                required: false,
                is_enum: false,
                single_char: false,
            });
        }
    }
    out
}

fn emit_struct(s: &mut String, fields: &[&RField]) {
    s.push_str("pub struct HeaderDecoder<'buf> {\n");
    s.push_str("    pub reader: nexus_fix_codec::FieldReader<'buf>,\n");
    for f in fields {
        let _ = writeln!(s, "    {}: nexus_fix_codec::FieldSpan,", snake(&f.name));
    }
    s.push_str("}\n\n");
}

fn emit_decode(s: &mut String, fields: &[&RField]) {
    s.push_str("impl<'buf> HeaderDecoder<'buf> {\n");
    s.push_str("    pub fn decode(buf: &'buf [u8]) -> Self {\n");
    s.push_str("        let mut h = Self {\n");
    s.push_str("            reader: nexus_fix_codec::FieldReader::new(buf, 0),\n");
    for f in fields {
        let _ = writeln!(
            s,
            "            {}: nexus_fix_codec::FieldSpan::EMPTY,",
            snake(&f.name)
        );
    }
    s.push_str("        };\n");
    // Forward-only boundary peek: consume header tags, and stop *without*
    // consuming the first non-header tag, so the body decoder reads it with no
    // re-scan (the tag is read locally; this field's SOH is never scanned here).
    let pred = fields
        .iter()
        .map(|f| f.number.to_string())
        .collect::<Vec<_>>()
        .join(" | ");
    let _ = writeln!(
        s,
        "        while let Some(f) = h.reader.next_field_if(|tag| matches!(tag, {pred})) {{"
    );
    s.push_str("            match f.tag {\n");
    for f in fields {
        let _ = writeln!(
            s,
            "                {} => h.{} = f.value,",
            f.number,
            snake(&f.name)
        );
    }
    s.push_str("                _ => {}\n");
    s.push_str("            }\n");
    s.push_str("        }\n");
    s.push_str("        h\n");
    s.push_str("    }\n\n");
    s.push_str("    #[inline]\n");
    s.push_str("    pub fn buf(&self) -> &'buf [u8] {\n");
    s.push_str("        self.reader.buf()\n");
    s.push_str("    }\n");
    s.push_str("}\n\n");
}

fn emit_fix_header_impl(s: &mut String, fields: &[&RField]) -> Result<(), EmitError> {
    s.push_str("impl<'buf> nexus_fix_codec::FixHeader<'buf> for HeaderDecoder<'buf> {\n");
    s.push_str("    fn decode(buf: &'buf [u8]) -> Self {\n");
    s.push_str("        Self::decode(buf)\n");
    s.push_str("    }\n\n");

    let trait_methods: &[(&str, u32, &str)] = &[
        ("raw_msg_type", 35, "&'buf [u8]"),
        ("msg_seq_num", 34, "u64"),
        ("sender_comp_id", 49, "&'buf nexus_fix_codec::AsciiTextStr"),
        ("target_comp_id", 56, "&'buf nexus_fix_codec::AsciiTextStr"),
        ("poss_dup_flag", 43, "bool"),
        ("sending_time", 52, "nexus_fix_codec::FixTimestamp"),
    ];

    for &(method, tag, ty) in trait_methods {
        let field_name = match fields.iter().find(|f| f.number == tag) {
            Some(f) => snake(&f.name),
            None => return Err(EmitError::MissingSessionTag(tag)),
        };
        let _ = write!(
            s,
            "    fn {method}(&self) -> Option<nexus_fix_codec::FieldView<'buf, {ty}>> {{\n        \
             nexus_fix_codec::FieldView::new(self.{field_name}, self.reader.buf())\n    \
             }}\n\n"
        );
    }
    s.push_str("}\n\n");
    Ok(())
}

fn emit_msg_type_accessor(s: &mut String) {
    s.push_str("impl HeaderDecoder<'_> {\n");
    s.push_str("    pub fn msg_type(&self) -> Option<super::MsgType> {\n");
    s.push_str("        if self.msg_type.is_present() {\n");
    s.push_str("            super::MsgType::from_bytes(self.msg_type.slice(self.reader.buf()))\n");
    s.push_str("        } else {\n");
    s.push_str("            None\n");
    s.push_str("        }\n");
    s.push_str("    }\n");
    s.push_str("}\n\n");
}

fn emit_accessors(s: &mut String, fields: &[&RField]) {
    s.push_str("impl<'buf> HeaderDecoder<'buf> {\n");
    let buf_expr = "self.reader.buf()";
    for f in fields {
        if f.number == 35 {
            continue;
        }
        emit_value_accessor(s, f, buf_expr);
    }
    s.push_str("}\n");
}
