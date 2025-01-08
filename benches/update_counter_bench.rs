use criterion::{black_box, criterion_group, criterion_main, Criterion};
use dm_unit::emulator::branch_predictor::BranchPredictor; // Adjust the path as needed
use rand::prelude::*;

fn bench_update_counter(c: &mut Criterion) {
    let mut predictor = BranchPredictor::default();
    let index = 0u16;

    let taken: Vec<bool> = (0..1000000).map(|_| rand::random()).collect();

    c.bench_function("update_counter_branchless", |b| {
        b.iter(|| {
            for t in &taken {
                predictor.update_counter(black_box(index), black_box(*t));
            }
        })
    });
}

criterion_group!(benches, bench_update_counter);
criterion_main!(benches);
