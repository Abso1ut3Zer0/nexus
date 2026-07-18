use crate::dict::{self, FieldType};
use crate::emit;

const SAMPLE: &str = include_str!("../tests/fixtures/venue_alpha.xml");

fn file<'a>(files: &'a [emit::GeneratedFile], name: &str) -> &'a str {
    files
        .iter()
        .find(|f| f.name == name)
        .map_or_else(|| panic!("missing {name}"), |f| f.source.as_str())
}

#[test]
fn parses_structure() {
    let d = dict::parse(SAMPLE).unwrap();
    assert_eq!(d.major, "4");
    assert_eq!(d.minor, "4");
    assert_eq!(d.messages.len(), 3);
    assert!(d.field("Side").unwrap().is_enum());
    assert!(d.field("Side").unwrap().single_char());
    assert_eq!(d.field("RawData").unwrap().ftype, FieldType::Data);
    assert!(d.component("Parties").is_some());
}

#[test]
fn emits_tag_consts_and_enum() {
    let d = dict::parse(SAMPLE).unwrap();
    let files = emit::generate(&d).unwrap();
    let fields = file(&files, "fields.rs");
    assert!(fields.contains("pub const TAG_SIDE: u32 = 54;"));
    assert!(fields.contains("pub enum Side"));
    assert!(fields.contains("fn from_byte"));
}

#[test]
fn emits_message_decoder_and_group() {
    let d = dict::parse(SAMPLE).unwrap();
    let files = emit::generate(&d).unwrap();
    let messages = file(&files, "messages.rs");
    assert!(messages.contains("pub struct NewOrderSingle<'buf>"));
    assert!(messages.contains("pub fn wrap(header: super::header::HeaderDecoder<'buf>) -> Result<Self, nexus_fix_codec::DecodeError>"));
    assert!(
        messages.contains(
            "pub fn decode(buf: &'buf [u8]) -> Result<Self, nexus_fix_codec::DecodeError>"
        )
    );
    assert!(messages.contains("pub fn is_complete(&self) -> bool"));
    assert!(messages.contains("pub fn header(&self) -> &super::header::HeaderDecoder<'buf>"));
    let groups = file(&files, "groups.rs");
    assert!(groups.contains("NewOrderSingleNoPartyIDsEntry"));
    assert!(groups.contains("NewOrderSingleNoPartyIDsNoPartySubIDsEntry"));
}

#[test]
fn emits_msgtype_dispatch_and_begin_string() {
    let d = dict::parse(SAMPLE).unwrap();
    let files = emit::generate(&d).unwrap();
    let m = file(&files, "mod.rs");
    assert!(m.contains("pub const BEGIN_STRING: &[u8] = b\"FIX.4.4\";"));
    assert!(m.contains("enum MsgType"));
    assert!(m.contains("b\"D\" => Some(Self::NewOrderSingle)"));
    assert!(m.contains("pub struct Dict;"));
    assert!(m.contains("impl nexus_fix_codec::FixDictionary for Dict"));
    assert!(m.contains("type Header<'buf> = header::HeaderDecoder<'buf>;"));
    assert!(m.contains("fn is_admin(msg_type: MsgType) -> bool"));
    assert!(m.contains("MsgType::Heartbeat"));
    assert!(m.contains("pub mod header { include!(\"header.rs\"); }"));
}

#[test]
fn emits_generated_header_decoder() {
    let d = dict::parse(SAMPLE).unwrap();
    let files = emit::generate(&d).unwrap();
    let h = file(&files, "header.rs");
    assert!(h.contains("pub struct HeaderDecoder<'buf>"));
    assert!(h.contains("pub fn decode(buf: &'buf [u8]) -> Self"));
    assert!(h.contains(
        "pub fn msg_type(&self) -> Result<super::MsgType, nexus_fix_codec::UnknownMsgType<'buf>>"
    ));
    assert!(h.contains("impl<'buf> nexus_fix_codec::FixHeader<'buf> for HeaderDecoder<'buf>"));
    assert!(h.contains("fn raw_msg_type(&self)"));
    assert!(h.contains("fn msg_seq_num(&self)"));
    assert!(h.contains("fn sender_comp_id(&self)"));
    // Dict-specific header field
    assert!(h.contains("sender_sub_id"));
}

#[test]
fn parses_header_and_trailer() {
    let d = dict::parse(SAMPLE).unwrap();
    assert!(!d.header.is_empty());
    assert!(!d.trailer.is_empty());
}

#[test]
fn rejects_data_in_group() {
    let xml = r#"<fix major="4" minor="4">
      <messages>
        <message name="M" msgtype="X">
          <group name="NoThings" required="N">
            <field name="ThingLen" required="N"/>
            <field name="ThingData" required="N"/>
          </group>
        </message>
      </messages>
      <fields>
        <field number="100" name="NoThings" type="NUMINGROUP"/>
        <field number="101" name="ThingLen" type="LENGTH"/>
        <field number="102" name="ThingData" type="DATA"/>
      </fields>
    </fix>"#;
    let d = dict::parse(xml).unwrap();
    assert!(matches!(
        emit::generate(&d),
        Err(emit::EmitError::DataInGroup(_))
    ));
}
