use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};
use std::fs;
use std::path::Path;

use bincode::Encode;
use serde::{Deserialize, Serialize};
use wincode_derive::{SchemaRead, SchemaWrite};

#[derive(
    Serialize, Deserialize, Encode, Debug, PartialEq, Clone, SchemaRead, SchemaWrite
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
}

fn write(path: &Path, bytes: &[u8]) {
    if let Some(dir) = path.parent() {
        fs::create_dir_all(dir).unwrap();
    }
    fs::write(path, bytes).unwrap();
}

fn seeds() -> Vec<(String, AllTypes)> {
    let mut out = Vec::new();

    // Maps / sets
    let mut bmap = BTreeMap::new(); bmap.insert(1, 2); bmap.insert(10, 20);
    out.push(("btree_map".into(), AllTypes::BTreeMap(bmap)));

    let mut hmap = HashMap::new(); hmap.insert(5, 15); hmap.insert(100, 200);
    out.push(("hash_map".into(), AllTypes::HashMap(hmap)));

    let mut bset = BTreeSet::new(); bset.insert(1); bset.insert(99);
    out.push(("btree_set".into(), AllTypes::BTreeSet(bset)));

    let mut hset = HashSet::new(); hset.insert(2); hset.insert(3);
    out.push(("hash_set".into(), AllTypes::HashSet(hset)));

    // Vectors and sequences
    let seq = AllTypes::Vec(vec![
        AllTypes::U8(1),
        AllTypes::U8(2),
        AllTypes::String("hi".into())
    ]);
    out.push(("vec_basic".into(), seq.clone()));

    let mut dq = VecDeque::new();
    dq.push_back(AllTypes::I8(-5));
    dq.push_back(AllTypes::U8(255));
    out.push(("vecdeque".into(), AllTypes::VecDeque(dq)));

    // Strings & bytes
    out.push(("string".into(), AllTypes::String("hello".into())));
    out.push(("bytes".into(), AllTypes::Bytes(vec![0, 1, 2, 3, 255])));

    // Optionals and nested
    out.push(("opt_none".into(), AllTypes::Opt(None)));
    out.push(("opt_some".into(), AllTypes::Opt(Some(Box::new(AllTypes::U8(42))))));
    out.push((
        "nested_box".into(),
        AllTypes::Box(Box::new(AllTypes::Vec(vec![
            AllTypes::String("nest".into()),
            AllTypes::U8(7),
        ]))),
    ));
    out.push((
        "boxslice".into(),
        AllTypes::BoxSlice(vec![AllTypes::U8(3), AllTypes::U8(4)].into_boxed_slice()),
    ));

    // Integers
    out.push(("i8_min".into(), AllTypes::I8(i8::MIN)));
    out.push(("i8_max".into(), AllTypes::I8(i8::MAX)));
    out.push(("u8_max".into(), AllTypes::U8(u8::MAX)));
    out.push(("i128_neg".into(), AllTypes::I128(-123456789)));
    out.push(("i128_max".into(), AllTypes::I128(i128::MAX)));
    out.push(("u128_big".into(), AllTypes::U128((1u128 << 100) + 99)));

    out
}

fn main() {
    let out_win_bin = Path::new("corpus/win_bin");
    let out_diff = Path::new("corpus/differential");

    let b_legacy = bincode::config::legacy().with_limit::<1_000_000>();

    for (name, val) in seeds() {
        // --- bincode (legacy) ---
        let bl = bincode::encode_to_vec(&val, b_legacy).expect("bincode encode");
        write(&out_legacy.join(format!("bincode-legacy-{}.bin", name)), &bl);
        write(&out_diff.join(format!("bincode-legacy-{}.bin", name)), &bl);

        // --- wincode ---
        let ww = wincode::serialize(&val).expect("wincode encode");
        write(&out_legacy.join(format!("wincode-{}.bin", name)), &ww);
        write(&out_diff.join(format!("wincode-{}.bin", name)), &ww);
    }

    println!("✅ Seeds written to:");
    println!("  corpus/win_bin/");
    println!("  corpus/differential/");
}
