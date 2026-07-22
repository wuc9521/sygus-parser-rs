use criterion::{black_box, criterion_group, criterion_main, Criterion};
use sygus_parser::ast::SyGuSFile;

// Test corpus embedded at compile time so file IO stays out of the timed loop.
const CASES: &[(&str, &str)] = &[
    (
        "define-sort-test",
        include_str!("../tests/define-sort-test.sl"),
    ),
    ("forall", include_str!("../tests/forall.sl")),
    ("hd-01", include_str!("../tests/hd-01.sl")),
    ("hd-22", include_str!("../tests/hd-22.sl")),
];

fn bench_parse(c: &mut Criterion) {
    let mut group = c.benchmark_group("SyGuSFile::from_str");
    for (name, src) in CASES {
        group.bench_function(*name, |b| {
            b.iter(|| SyGuSFile::from_str(black_box(src)).expect(name));
        });
    }
    group.finish();
}

criterion_group!(benches, bench_parse);
criterion_main!(benches);
