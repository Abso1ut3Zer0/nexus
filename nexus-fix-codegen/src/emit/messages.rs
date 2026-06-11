use std::collections::{HashMap, HashSet};
use std::fmt::Write;

use crate::dict::FieldType;

use super::{
    HEADER, RField, RGroup, RMember, RMessage, emit_group_accessor, emit_value_accessor,
    group_type, pascal, screaming, snake, subtree_tags, tag_or,
};

enum Top<'a> {
    Field(&'a RField),
    Group(&'a RGroup),
}

pub fn emit(messages: &[RMessage]) -> String {
    let mut s = String::new();
    s.push_str(HEADER);
    for m in messages {
        emit_message(&mut s, m);
    }
    s
}

fn emit_message(s: &mut String, m: &RMessage) {
    let ty = pascal(&m.name);
    let tops: Vec<Top> = m
        .members
        .iter()
        .map(|mem| match mem {
            RMember::Field(f) => Top::Field(f),
            RMember::Group(g) => Top::Group(g),
        })
        .collect();

    let mut data_handled: HashSet<u32> = HashSet::new();
    let mut data_after: HashMap<u32, &RField> = HashMap::new();
    for w in tops.windows(2) {
        if let [Top::Field(l), Top::Field(d)] = w
            && l.ftype == FieldType::Length
            && d.ftype == FieldType::Data
        {
            data_handled.insert(d.number);
            data_after.insert(l.number, *d);
        }
    }

    emit_struct(s, &ty, &tops);
    let _ = writeln!(s, "impl<'buf> {ty}<'buf> {{");
    emit_wrap(s, &ty, &tops, &data_handled, &data_after);
    emit_decode(s);
    emit_is_complete(s, &tops);
    emit_header_delegates(s);
    emit_accessors(s, &tops, &m.name);
    s.push_str("}\n\n");
}

fn emit_struct(s: &mut String, ty: &str, tops: &[Top]) {
    let _ = writeln!(
        s,
        "pub struct {ty}<'buf> {{\n    header: super::header::HeaderDecoder<'buf>,"
    );
    let mut seen = HashSet::new();
    for t in tops {
        match t {
            Top::Field(f) if seen.insert(f.number) => {
                let _ = writeln!(s, "    {}: nexus_fix_codec::FieldSpan,", snake(&f.name));
            }
            Top::Group(g) if seen.insert(g.number) => {
                let _ = writeln!(s, "    {}: nexus_fix_codec::GroupSpan,", snake(&g.name));
            }
            _ => {}
        }
    }
    s.push_str("    checksum: nexus_fix_codec::FieldSpan,\n");
    s.push_str("}\n\n");
}

fn emit_wrap(
    s: &mut String,
    _ty: &str,
    tops: &[Top],
    data_handled: &HashSet<u32>,
    data_after: &HashMap<u32, &RField>,
) {
    // Build the shared decode body (struct init + field loop) once, then emit it
    // into BOTH wrap_unchecked and wrap. The body is *duplicated* rather than
    // factored into a shared call: a shared `wrap_unchecked()` call would return
    // the (large) message struct by value, adding a struct move on the hot
    // checked path. Each entry point builds the message in its own frame.
    let mut body = String::new();
    body.push_str("        let mut m = Self {\n            header,\n");
    let mut seen = HashSet::new();
    for t in tops {
        match t {
            Top::Field(f) if seen.insert(f.number) => {
                let _ = writeln!(
                    body,
                    "            {}: nexus_fix_codec::FieldSpan::EMPTY,",
                    snake(&f.name)
                );
            }
            Top::Group(g) if seen.insert(g.number) => {
                let _ = writeln!(
                    body,
                    "            {}: nexus_fix_codec::GroupSpan::EMPTY,",
                    snake(&g.name)
                );
            }
            _ => {}
        }
    }
    body.push_str("            checksum: nexus_fix_codec::FieldSpan::EMPTY,\n");
    body.push_str("        };\n");

    let mut arms: Vec<(String, String)> = Vec::new();
    let mut seen_arm = HashSet::new();
    for t in tops {
        match t {
            Top::Field(f) => {
                if data_handled.contains(&f.number) || !seen_arm.insert(f.number) {
                    continue;
                }
                if let Some(d) = data_after.get(&f.number) {
                    arms.push((screaming(&f.name), data_body(f, d)));
                } else {
                    arms.push((
                        screaming(&f.name),
                        format!("                m.{} = f.value;\n", snake(&f.name)),
                    ));
                }
            }
            Top::Group(g) => {
                if !seen_arm.insert(g.number) {
                    continue;
                }
                arms.push((screaming(&g.name), group_body(g)));
            }
        }
    }

    if !arms.is_empty() {
        let needs_buf = arms.iter().any(|(_, arm_body)| arm_body.contains("buf"));
        if needs_buf {
            body.push_str("        let buf = m.header.reader.buf();\n");
        }
        emit_wrap_loop(&mut body, &arms);
    }

    // wrap_unchecked: scan + dispatch, no checksum verification.
    s.push_str("    /// Decode the message body **without** verifying the FIX checksum.\n");
    s.push_str("    ///\n");
    s.push_str("    /// For trusted feeds only — replay, internal links, already-validated\n");
    s.push_str("    /// data. Prefer [`wrap`](Self::wrap) for counterparty data.\n");
    s.push_str(
        "    pub fn wrap_unchecked(header: super::header::HeaderDecoder<'buf>) -> Result<Self, nexus_fix_codec::DecodeError> {\n",
    );
    s.push_str(&body);
    s.push_str("        Ok(m)\n    }\n\n");

    // wrap: same body, then verify the checksum.
    s.push_str("    /// Decode the message body and verify the FIX checksum (tag 10).\n");
    s.push_str(
        "    pub fn wrap(header: super::header::HeaderDecoder<'buf>) -> Result<Self, nexus_fix_codec::DecodeError> {\n",
    );
    s.push_str(&body);
    // Verify the CheckSum iff tag 10 was *seen* (the span is no longer EMPTY),
    // not iff it has a non-empty value. A present-but-empty CheckSum (`10=\x01`)
    // is malformed and must be rejected; gating on `is_present()` (len > 0) would
    // skip it and accept the message, diverging from `validate_checksum`. The
    // empty value falls into `verify_checksum`, which rejects it.
    s.push_str("        if m.checksum != nexus_fix_codec::FieldSpan::EMPTY {\n");
    s.push_str(
        "            m.header.reader.verify_checksum(m.checksum).map_err(nexus_fix_codec::DecodeError::Checksum)?;\n",
    );
    s.push_str("        }\n");
    s.push_str("        Ok(m)\n    }\n\n");
}

fn emit_wrap_loop(s: &mut String, arms: &[(String, String)]) {
    // The header stopped at the first body field without consuming it; scan on.
    s.push_str("        while let Some(f) = m.header.reader.next_field() {\n");
    s.push_str("            match f.tag {\n");
    for (tag, body) in arms {
        let _ = writeln!(s, "                super::fields::TAG_{tag} => {{");
        s.push_str(body);
        s.push_str("                }\n");
    }
    // CheckSum (tag 10) is the FIX message terminator. Record it and stop —
    // anything after it is trailing data, not part of this message, and must not
    // be scanned into field spans.
    s.push_str("                10 => {\n");
    s.push_str("                    m.checksum = f.value;\n");
    s.push_str("                    break;\n");
    s.push_str("                }\n");
    s.push_str("                _ => {}\n            }\n");
    s.push_str("        }\n");
}

fn emit_decode(s: &mut String) {
    s.push_str("    /// Decode the message and verify the FIX checksum (tag 10).\n");
    s.push_str(
        "    pub fn decode(buf: &'buf [u8]) -> Result<Self, nexus_fix_codec::DecodeError> {\n",
    );
    s.push_str("        Self::wrap(super::header::HeaderDecoder::decode(buf))\n");
    s.push_str("    }\n\n");
    s.push_str("    /// Decode **without** verifying the FIX checksum — for trusted feeds.\n");
    s.push_str(
        "    pub fn decode_unchecked(buf: &'buf [u8]) -> Result<Self, nexus_fix_codec::DecodeError> {\n",
    );
    s.push_str("        Self::wrap_unchecked(super::header::HeaderDecoder::decode(buf))\n");
    s.push_str("    }\n\n");
}

fn data_body(len: &RField, data: &RField) -> String {
    let mut b = String::new();
    let _ = writeln!(b, "                m.{} = f.value;", snake(&len.name));
    b.push_str("                let (n, _) = nexus_fix_codec::parse_tag(f.value.slice(buf));\n");
    b.push_str("                let data_f = m.header.reader.next_data_field(n as usize)?;\n");
    let _ = writeln!(b, "                m.{} = data_f.value;", snake(&data.name));
    b
}

fn group_body(g: &RGroup) -> String {
    let mut tags = Vec::new();
    subtree_tags(&g.members, &mut tags);
    let pat = tag_or(&tags);
    let mut b = String::new();
    b.push_str(
        "                let (count, _) = nexus_fix_codec::parse_tag(f.value.slice(buf));\n",
    );
    let _ = writeln!(
        b,
        "                m.{} = nexus_fix_codec::GroupSpan::new(m.header.reader.pos() as u32, count.min(u16::MAX as u32) as u16);",
        snake(&g.name)
    );
    // Consume group fields; stop *without* consuming the first non-group field
    // (forward-only peek) so the outer loop reads it with no re-scan.
    let _ = writeln!(
        b,
        "                while m.header.reader.next_field_if(|tag| matches!(tag, {pat})).is_some() {{}}"
    );
    b
}

fn emit_is_complete(s: &mut String, tops: &[Top]) {
    let mut conds = Vec::new();
    let mut seen = HashSet::new();
    for t in tops {
        match t {
            Top::Field(f) if f.required && seen.insert(f.number) => {
                conds.push(format!("self.{}.is_present()", snake(&f.name)));
            }
            Top::Group(g) if g.required && seen.insert(g.number) => {
                conds.push(format!("self.{}.is_present()", snake(&g.name)));
            }
            _ => {}
        }
    }
    let body = if conds.is_empty() {
        "true".to_string()
    } else {
        conds.join(" && ")
    };
    let _ = writeln!(
        s,
        "    pub fn is_complete(&self) -> bool {{\n        {body}\n    }}\n"
    );
}

fn emit_header_delegates(s: &mut String) {
    s.push_str(
        "    pub fn header(&self) -> &super::header::HeaderDecoder<'buf> { &self.header }\n\n",
    );
}

fn emit_accessors(s: &mut String, tops: &[Top], msg_name: &str) {
    let prefix = pascal(msg_name);
    let buf_expr = "self.header.reader.buf()";
    let mut seen = HashSet::new();
    for t in tops {
        match t {
            Top::Field(f) if seen.insert(f.number) => emit_value_accessor(s, f, buf_expr),
            Top::Group(g) if seen.insert(g.number) => {
                let view = format!("{}View", group_type(&prefix, &g.name));
                emit_group_accessor(s, &snake(&g.name), &view, buf_expr);
            }
            _ => {}
        }
    }
}
