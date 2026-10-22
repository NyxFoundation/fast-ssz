use criterion::{criterion_group, criterion_main, Criterion};
use nyx_ssz::{
    bytecollections::ByteList,
    codec::Ssz,
    collections::{list, List},
    proof,
};
use std::{hint::black_box, time::Duration};

#[derive(nyx_ssz::Ssz)]
struct Record {
    slot: u64,
    payload: ByteList<4096>,
    votes: List<u64, 1024>,
}

fn benchmarks(c: &mut Criterion) {
    let value = Record {
        slot: 42,
        payload: ByteList::from_bytes(vec![7; 4096]).unwrap(),
        votes: list(vec![1; 1024]).unwrap(),
    };
    let bytes = value.encode().unwrap();
    c.bench_function("container/encode/12304-bytes", |b| {
        b.iter(|| black_box(&value).encode().unwrap())
    });
    c.bench_function("container/decode/12304-bytes", |b| {
        b.iter(|| Record::decode(black_box(&bytes)).unwrap())
    });
    c.bench_function("container/root/12304-bytes", |b| {
        b.iter(|| black_box(&value).hash_tree_root().unwrap())
    });
    c.bench_function("container/single-proof", |b| {
        b.iter(|| proof::create(black_box(&value), 4).unwrap())
    });
    c.bench_function("container/multiproof", |b| {
        b.iter(|| proof::create_multi(black_box(&value), &[4, 6, 10]).unwrap())
    });
}

criterion_group! {
    name = codec;
    config = Criterion::default().sample_size(10).warm_up_time(Duration::from_secs(1)).measurement_time(Duration::from_secs(1));
    targets = benchmarks
}
criterion_main!(codec);
