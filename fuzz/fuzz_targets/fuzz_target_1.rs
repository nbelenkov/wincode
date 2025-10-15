#![no_main]
use libfuzzer_sys::fuzz_target;

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};
use std::ffi::CString;
use std::net::{IpAddr, Ipv4Addr, Ipv6Addr, SocketAddr, SocketAddrV4, SocketAddrV6};
use std::num::{NonZeroI128, NonZeroI32, NonZeroU128, NonZeroU32, NonZeroU64};
use std::path::PathBuf;
use std::rc::Rc;
use std::sync::Arc;
use std::time::{Duration, SystemTime};

use wincode_derive::{SchemaWrite, SchemaRead};

#[derive(SchemaWrite, SchemaRead, PartialEq, Debug)]
enum AllTypes {
    BTreeMap(BTreeMap<u8, u8>),
    HashMap(HashMap<u8, u8>),
    HashSet(HashSet<u8>),
    BTreeSet(BTreeSet<u8>),
    VecDeque(VecDeque<AllTypes>),
    Vec(Vec<AllTypes>),
    String(String),
    Box(Box<AllTypes>),
    BoxSlice(Box<[AllTypes]>),
    Rc(Rc<AllTypes>),
    Arc(Arc<AllTypes>),
    Bytes(Vec<u8>),
    Opt(Option<Box<AllTypes>>),
    I128(i128),
    I8(i8),
    U128(u128),
    U8(u8),
    // Cow(Cow<'static, [u8]>), Blocked, see comment on decode
}



fuzz_target!(|data: &[u8]| {

    let result = wincode::deserialize::<AllTypes>(data);

    if data.len() > 16 * 1024 { return; }

    if let Ok(before) = result {
        // serialize -> Vec<u8>
        let encoded = wincode::serialize(&before).expect("serialize");
        // deserialize back to the same type
        let after: AllTypes = wincode::deserialize(&encoded).expect("deserialize round-trip");
        assert_eq!(before, after);
    }
});
