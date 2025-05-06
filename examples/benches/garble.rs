// Copyright 2024-2025 Irreducible Inc.

use std::{
	collections::BTreeMap,
	fs::File,
	io::{self, BufRead},
	path::Path,
};

use anyhow::Result;
use binius_circuits::{
	builder::{types::U, ConstraintSystemBuilder},
	garble::{Gate, Label, WitnessedGate, WitnessedLabel},
};
use binius_core::{
	constraint_system::{self, ConstraintSystem, Proof},
	fiat_shamir::HasherChallenger,
	witness::MultilinearExtensionIndex,
};
use binius_field::{
	arch::OptimalUnderlier, as_packed_field::PackedType, tower::CanonicalTowerFamily,
	BinaryField128b,
};
use binius_hal::{make_portable_backend, CpuBackend};
use binius_hash::groestl::{Groestl256, Groestl256ByteCompression};
use binius_utils::rayon::adjust_thread_pool;
use bytesize::ByteSize;
use criterion::{criterion_group, criterion_main, BatchSize, Criterion};
use rand::thread_rng;

const LOG_INV_RATE: usize = 1;
const SECURITY_BITS: usize = 100;

fn witness_gen<'a>(
	allocator: &'a bumpalo::Bump,
	filename: String,
) -> (
	ConstraintSystem<BinaryField128b>,
	MultilinearExtensionIndex<'a, PackedType<OptimalUnderlier, BinaryField128b>>,
	CpuBackend,
) {
	adjust_thread_pool()
		.as_ref()
		.expect("failed to init thread pool");

	let mut builder = ConstraintSystemBuilder::new_with_witness(&allocator);
	let trace_gen_scope = tracing::info_span!("generating trace").entered();

	let rng = &mut thread_rng();

	if let Ok(lines) = read_lines(filename) {
		let mut witnessed_wires =
			BTreeMap::<usize, ((Label, Label), (WitnessedLabel, WitnessedLabel))>::new();
		let mut witness_wire = |idx: usize,
		                        builder: &mut ConstraintSystemBuilder<'_>|
		 -> ((Label, Label), (WitnessedLabel, WitnessedLabel)) {
			match witnessed_wires.get(&idx) {
				Some(labels) => *labels,
				_ => {
					let labels = (Label::random(idx, rng), Label::random(idx, rng));
					let witnessed_labels = (labels.0.witness(builder), labels.1.witness(builder));
					witnessed_wires.insert(idx, (labels, witnessed_labels));
					(labels, witnessed_labels)
				}
			}
		};

		// Consumes the iterator, returns an (Optional) String
		for line in lines.map_while(Result::ok) {
			let line: Vec<_> = line.split_whitespace().collect();
			if line.last() == Some(&"AND") {
				let left = witness_wire(str::parse(line[2]).unwrap(), &mut builder);
				let right = witness_wire(str::parse(line[3]).unwrap(), &mut builder);
				let out = witness_wire(str::parse(line[4]).unwrap(), &mut builder);

				let gate = Gate {
					left: left.0,
					right: right.0,
					out: out.0,
				};
				let output = gate
					.garble_and_gate(&mut thread_rng())
					.iter()
					.map(|output| output.witness(&mut builder))
					.collect::<Vec<_>>()
					.try_into()
					.unwrap();
				let witnessed_gate = WitnessedGate { out: out.1, output };

				witnessed_gate.garble_and_gate(&mut builder).unwrap();
			}
		}
	}

	drop(trace_gen_scope);

	let witness = builder
		.take_witness()
		.expect("builder created with witness");

	let constraint_system = builder.build().unwrap();

	let backend = make_portable_backend();

	(constraint_system, witness, backend)
}

fn prove<'a>(
	constraint_system: ConstraintSystem<binius_field::BinaryField128b>,
	witness: MultilinearExtensionIndex<'a, PackedType<OptimalUnderlier, BinaryField128b>>,
	backend: CpuBackend,
) -> (ConstraintSystem<binius_field::BinaryField128b>, Proof) {
	let proof = constraint_system::prove::<
		U,
		CanonicalTowerFamily,
		Groestl256,
		Groestl256ByteCompression,
		HasherChallenger<Groestl256>,
		_,
	>(&constraint_system, LOG_INV_RATE, SECURITY_BITS, &[], witness, &backend)
	.unwrap();

	println!("Proof size: {}", ByteSize::b(proof.get_proof_size() as u64));

	(constraint_system, proof)
}

fn verify(constraint_system: ConstraintSystem<binius_field::BinaryField128b>, proof: Proof) {
	constraint_system::verify::<
		U,
		CanonicalTowerFamily,
		Groestl256,
		Groestl256ByteCompression,
		HasherChallenger<Groestl256>,
	>(&constraint_system, LOG_INV_RATE, SECURITY_BITS, &[], proof)
	.unwrap();
}

// The output is wrapped in a Result to allow matching on errors.
// Returns an Iterator to the Reader of the lines of the file.
fn read_lines<P>(filename: P) -> io::Result<io::Lines<io::BufReader<File>>>
where
	P: AsRef<Path>,
{
	let file = File::open(filename).unwrap();
	Ok(io::BufReader::new(file).lines())
}

// adder64: 63 ANDs
fn garble_adder64(c: &mut Criterion) {
	let mut group = c.benchmark_group("garble_adder64");
	group.sample_size(10);
	let allocator = bumpalo::Bump::new();

	group.bench_function("prove", |bench| {
		bench.iter_batched(
			|| witness_gen(&allocator, "./benches/adder64".to_string()),
			|(constraint_system, witness, backend)| {
				prove(constraint_system, witness, backend);
			},
			BatchSize::SmallInput,
		);
	});

	group.bench_function("verify", |bench| {
		bench.iter_batched(
			|| {
				let (constraint_system, witness, backend) =
					witness_gen(&allocator, "./benches/adder64".to_string());
				prove(constraint_system, witness, backend)
			},
			|(constraint_system, proof)| {
				verify(constraint_system, proof);
			},
			BatchSize::SmallInput,
		);
	});

	group.finish();
}

// fp_lt: 381 ANDs
fn garble_fp_lt(c: &mut Criterion) {
	let mut group = c.benchmark_group("garble_fp_lt");
	group.sample_size(10);
	let allocator = bumpalo::Bump::new();

	group.bench_function("prove", |bench| {
		bench.iter_batched(
			|| witness_gen(&allocator, "./benches/fp_lt".to_string()),
			|(constraint_system, witness, backend)| {
				prove(constraint_system, witness, backend);
			},
			BatchSize::SmallInput,
		);
	});

	group.bench_function("verify", |bench| {
		bench.iter_batched(
			|| {
				let (constraint_system, witness, backend) =
					witness_gen(&allocator, "./benches/fp_lt".to_string());
				prove(constraint_system, witness, backend)
			},
			|(constraint_system, proof)| {
				verify(constraint_system, proof);
			},
			BatchSize::SmallInput,
		);
	});

	group.finish();
}

// fp_ceil: 650 ANDs
fn garble_fp_ceil(c: &mut Criterion) {
	let mut group = c.benchmark_group("garble_fp_ceil");
	group.sample_size(10);
	let allocator = bumpalo::Bump::new();

	group.bench_function("prove", |bench| {
		bench.iter_batched(
			|| witness_gen(&allocator, "./benches/fp_ceil".to_string()),
			|(constraint_system, witness, backend)| {
				prove(constraint_system, witness, backend);
			},
			BatchSize::SmallInput,
		);
	});

	group.bench_function("verify", |bench| {
		bench.iter_batched(
			|| {
				let (constraint_system, witness, backend) =
					witness_gen(&allocator, "./benches/fp_ceil".to_string());
				prove(constraint_system, witness, backend)
			},
			|(constraint_system, proof)| {
				verify(constraint_system, proof);
			},
			BatchSize::SmallInput,
		);
	});

	group.finish();
}

// fp_f2i: 1467 ANDs
fn garble_fp_f2i(c: &mut Criterion) {
	let mut group = c.benchmark_group("garble_fp_f2i");
	group.sample_size(10);
	let allocator = bumpalo::Bump::new();

	group.bench_function("prove", |bench| {
		bench.iter_batched(
			|| witness_gen(&allocator, "./benches/fp_f2i".to_string()),
			|(constraint_system, witness, backend)| {
				prove(constraint_system, witness, backend);
			},
			BatchSize::SmallInput,
		);
	});

	group.bench_function("verify", |bench| {
		bench.iter_batched(
			|| {
				let (constraint_system, witness, backend) =
					witness_gen(&allocator, "./benches/fp_f2i".to_string());
				prove(constraint_system, witness, backend)
			},
			|(constraint_system, proof)| {
				verify(constraint_system, proof);
			},
			BatchSize::SmallInput,
		);
	});

	group.finish();
}

// fp_i2f: 2416 ANDs
fn garble_fp_i2f(c: &mut Criterion) {
	let mut group = c.benchmark_group("garble_fp_i2f");
	group.sample_size(10);
	let allocator = bumpalo::Bump::new();

	group.bench_function("prove", |bench| {
		bench.iter_batched(
			|| witness_gen(&allocator, "./benches/fp_i2f".to_string()),
			|(constraint_system, witness, backend)| {
				prove(constraint_system, witness, backend);
			},
			BatchSize::SmallInput,
		);
	});

	group.bench_function("verify", |bench| {
		bench.iter_batched(
			|| {
				let (constraint_system, witness, backend) =
					witness_gen(&allocator, "./benches/fp_i2f".to_string());
				prove(constraint_system, witness, backend)
			},
			|(constraint_system, proof)| {
				verify(constraint_system, proof);
			},
			BatchSize::SmallInput,
		);
	});

	group.finish();
}

criterion_main!(garble);
criterion_group!(
	garble,
	garble_adder64,
	garble_fp_lt,
	garble_fp_ceil,
	garble_fp_f2i,
	garble_fp_i2f
);
