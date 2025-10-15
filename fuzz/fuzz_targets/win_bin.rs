#![no_main]
use libfuzzer_sys::fuzz_target;

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};

use serde::{Deserialize, Serialize};
use bincode::{Decode, Encode};
use wincode_derive::{SchemaRead, SchemaWrite};

const MAX_INPUT: usize = 16 * 1024;
const MAX_WIRE:  usize = 1 * 1024 * 1024; // skip cross-check if a re-encoding explodes past this

#[derive(
    Serialize, Deserialize,
    Encode, Decode,
    SchemaRead, SchemaWrite,
    Debug, PartialEq,
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
    U8(u8)
}

fn bincode_cfg() -> impl bincode::config::Config {
    bincode::config::legacy().with_limit::<1_000_000>() // big budget to avoid false negatives
}


fuzz_target!(|data: &[u8]| {
    if data.len() > MAX_INPUT { return; }

    // Try to get a value from each side independently.
    let bc = bincode::decode_from_slice::<AllTypes, _>(data, bincode_cfg());
    let wc = wincode::deserialize::<AllTypes>(data);

    // 1) bincode -> wincode cross-decode
    if let Ok((bval, _read)) = &bc {
        let enc_b = match bincode::encode_to_vec(bval, bincode_cfg()) {
            Ok(v) => v,
            Err(e) => { eprintln!("bincode re-encode failed: {e:?}"); panic!("bincode encode failed"); }
        };
        if enc_b.len() <= MAX_WIRE {
            match wincode::deserialize::<AllTypes>(&enc_b) {
                Ok(w_from_b) => {
                    if &w_from_b != bval {
                        eprintln!("bincode->wincode value mismatch");
                        eprintln!("bytes (bincode encoding): {:02x?}", &enc_b[..enc_b.len().min(256)]);
                        eprintln!("bincode: {:?}", bval);
                        eprintln!("wincode: {:?}", w_from_b);
                        panic!("bincode->wincode mismatch");
                    }
                }
                Err(e) => {
                    eprintln!("wincode failed to read bincode bytes: {e:?}");
                    eprintln!("bytes (bincode encoding): {:02x?}", &enc_b[..enc_b.len().min(256)]);
                    panic!("bincode->wincode decode error");
                }
            }
        }
    }

    // 2) wincode -> bincode cross-decode
    if let Ok(wval) = &wc {
        let enc_w = match wincode::serialize(wval) {
            Ok(v) => v,
            Err(e) => { eprintln!("wincode re-encode failed: {e:?}"); panic!("wincode encode failed"); }
        };
        if enc_w.len() <= MAX_WIRE {
            match bincode::decode_from_slice::<AllTypes, _>(&enc_w, bincode_cfg()) {
                Ok((b_from_w, _n)) => {
                    if &b_from_w != wval {
                        eprintln!("wincode->bincode value mismatch");
                        eprintln!("bytes (wincode encoding): {:02x?}", &enc_w[..enc_w.len().min(256)]);
                        eprintln!("wincode: {:?}", wval);
                        eprintln!("bincode: {:?}", b_from_w);
                        panic!("wincode->bincode mismatch");
                    }
                }
                Err(bincode::error::DecodeError::LimitExceeded) => {
                    // treat as inconclusive or raise the limit above
                    return;
                }
                Err(e) => {
                    eprintln!("bincode failed to read wincode bytes: {e:?}");
                    eprintln!("bytes (wincode encoding): {:02x?}", &enc_w[..enc_w.len().min(256)]);
                    panic!("wincode->bincode decode error");
                }
            }
        }
    }
});
