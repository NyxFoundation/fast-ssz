use criterion::{criterion_group, criterion_main, Criterion};
use libssz::{SszDecode, SszEncode};
use libssz_merkle::{HashTreeRoot, Sha2Hasher};
use nyx_ssz::codec::Ssz;
use nyx_ssz_bench_compare::{nyx, reference};
use std::{hint::black_box, time::Duration};

fn bench_nyx<T: Ssz>(c: &mut Criterion, schema: &str, value: T) {
    let bytes = value.encode().unwrap();
    c.bench_function(&format!("{schema}/encode/nyx"), |b| {
        b.iter(|| black_box(&value).encode().unwrap())
    });
    c.bench_function(&format!("{schema}/decode/nyx"), |b| {
        b.iter(|| T::decode(black_box(&bytes)).unwrap())
    });
    c.bench_function(&format!("{schema}/root/nyx"), |b| {
        b.iter(|| black_box(&value).hash_tree_root().unwrap())
    });
}

fn bench_reference<T: SszEncode + SszDecode + HashTreeRoot>(
    c: &mut Criterion,
    schema: &str,
    value: T,
) {
    let bytes = value.to_ssz();
    c.bench_function(&format!("{schema}/encode/libssz"), |b| {
        b.iter(|| black_box(&value).to_ssz())
    });
    c.bench_function(&format!("{schema}/decode/libssz"), |b| {
        b.iter(|| T::from_ssz_bytes(black_box(&bytes)).unwrap())
    });
    c.bench_function(&format!("{schema}/root/libssz"), |b| {
        b.iter(|| black_box(&value).hash_tree_root(&Sha2Hasher))
    });
    let mut buffer = Vec::with_capacity(bytes.len());
    c.bench_function(&format!("{schema}/encode_reuse/libssz"), |b| {
        b.iter(|| {
            buffer.clear();
            black_box(&value).ssz_append(&mut buffer);
            black_box(&buffer);
        })
    });
}

fn benchmarks(c: &mut Criterion) {
    black_box(nyx_ssz_bench_compare::fixtures());
    bench_nyx(c, "header", nyx::header());
    bench_reference(c, "header", reference::header());
    bench_nyx(c, "mixed", nyx::mixed());
    bench_reference(c, "mixed", reference::mixed());
}

criterion_group! {
    name = comparison;
    config = Criterion::default().sample_size(20).warm_up_time(Duration::from_secs(1)).measurement_time(Duration::from_secs(1));
    targets = benchmarks
}
criterion_main!(comparison);
