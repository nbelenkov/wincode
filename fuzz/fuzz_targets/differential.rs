#![no_main]
use libfuzzer_sys::fuzz_target;

use serde::{Deserialize, Serialize};
use wincode_derive::{SchemaRead, SchemaWrite};

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};
use solana_entry::entry::Entry;

// --- Your shared test type: must support *both* libraries.
#[derive(Serialize, Deserialize,
         bincode::Encode, bincode::Decode,         // bincode 2 derive (satisfies decode_from_slice)
         Debug, PartialEq,
         SchemaRead, SchemaWrite // wincode derives
)]
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
    Bytes(Vec<u8>),
    Opt(Option<Box<AllTypes>>),
    I128(i128),
    I8(i8),
    U128(u128),
    U8(u8),
    //Entry(Entry),
}

fuzz_target!(|data: &[u8]| {
    // Keep runs fast / avoid huge allocations on obviously huge blobs
    if data.len() > 80 * 1024 { return; }

    

    // --- bincode v2 decode (value + bytes_read)
    // Use a strict limit so absurd length prefixes don't explode allocations.
    let bcfg = bincode::config::legacy().with_limit::<1_000_000>();
    let b2: Result<(AllTypes, usize), bincode::error::DecodeError> =
        bincode::decode_from_slice(data, bcfg);

    // --- wincode decode (value only)
    let wc: Result<AllTypes, wincode::error::ReadError> =
        wincode::deserialize::<AllTypes>(data);


    match (&b2, &wc) {
        (Ok((bv, _read_b)), Ok(wv)) => {
            if bv != wv {
                eprintln!("DIFF: values differ on the same bytes");
                eprintln!("bytes: {:02x?}", data);
                eprintln!("bincode: {:?}", bv);
                eprintln!("wincode: {:?}", wv);
                panic!("differential mismatch: value inequality");
            }
        }
        (Ok((bv, _)), Err(e)) => {
            eprintln!("DIFF: bincode OK, wincode ERR");
            eprintln!("bytes: {:02x?}", data);
            eprintln!("bincode value: {:?}", bv);
            eprintln!("wincode err:   {:?}", e);
            eprintln!("differential mismatch: success vs error");
        }
        (Err(e), Ok(wv)) => {
            eprintln!("DIFF: bincode ERR, wincode OK");
            eprintln!("bytes: {:02x?}", data);
            eprintln!("bincode err:   {:?}", e);
            eprintln!("wincode value: {:?}", wv);
            eprintln!("differential mismatch: error vs success");
        }
        (Err(_), Err(_)) => {
            // Both rejected the input: not interesting by itself.
        }
    }
});