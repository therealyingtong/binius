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
	garble::{Label, WitnessedGate, WitnessedLabel},
};
use binius_core::{constraint_system, fiat_shamir::HasherChallenger};
use binius_field::tower::CanonicalTowerFamily;
use binius_hal::make_portable_backend;
use binius_hash::groestl::{Groestl256, Groestl256ByteCompression};
use binius_utils::rayon::adjust_thread_pool;
use bytesize::ByteSize;
use clap::{value_parser, Parser};
use rand::rngs::OsRng;
use tracing_profile::init_tracing;

#[derive(Debug, Parser)]
struct Args {
	/// The path to the Bristol fashion garbled circuit
	filename: String,
	/// The negative binary logarithm of the Reed–Solomon code rate.
	#[arg(long, default_value_t = 1, value_parser = value_parser!(u32).range(1..))]
	log_inv_rate: u32,
}

fn main() -> Result<()> {
	const SECURITY_BITS: usize = 100;

	adjust_thread_pool()
		.as_ref()
		.expect("failed to init thread pool");

	let args = Args::parse();
	let filename = args.filename;

	let _guard = init_tracing().expect("failed to initialize tracing");

	let allocator = bumpalo::Bump::new();
	let mut builder = ConstraintSystemBuilder::new_with_witness(&allocator);
	let trace_gen_scope = tracing::info_span!("generating trace").entered();

	let rng = &mut OsRng;

	if let Ok(lines) = read_lines(filename) {
		let witnessed_wires =
			BTreeMap::<usize, ((Label, Label), (WitnessedLabel, WitnessedLabel))>::new();
		let mut witness_wire = |idx: usize,
		                        builder: &mut ConstraintSystemBuilder<'_>|
		 -> ((Label, Label), (WitnessedLabel, WitnessedLabel)) {
			match witnessed_wires.get(&idx) {
				Some(labels) => *labels,
				_ => {
					let labels = (Label::random(idx, rng), Label::random(idx, rng));
					let witnessed_labels = (labels.0.witness(builder), labels.1.witness(builder));
					(labels, witnessed_labels)
				}
			}
		};

		// Consumes the iterator, returns an (Optional) String
		// let mut n_and_gates = 0;
		for line in lines.map_while(Result::ok) {
			let line: Vec<_> = line.split_whitespace().collect();
			if line.last() == Some(&"AND") {
				// println!("Garbling AND gate {}: {:?}", n_and_gates, line);
				// n_and_gates += 1;

				let left = witness_wire(str::parse(line[2])?, &mut builder);
				let right = witness_wire(str::parse(line[3])?, &mut builder);
				let out = witness_wire(str::parse(line[4])?, &mut builder);

				let gate = Gate {
					left: left.0,
					right: right.0,
					out: out.0,
				};
				let output = gate
					.garble_and_gate()
					.iter()
					.map(|output| output.witness(&mut builder))
					.collect::<Vec<_>>()
					.try_into()
					.unwrap();
				let witnessed_gate = WitnessedGate { out: out.1, output };

				witnessed_gate.garble_and_gate(&mut builder)?;
			}
		}
	}

	drop(trace_gen_scope);

	let witness = builder
		.take_witness()
		.expect("builder created with witness");

	let constraint_system = builder.build()?;

	let backend = make_portable_backend();

	let proof =
		constraint_system::prove::<
			U,
			CanonicalTowerFamily,
			Groestl256,
			Groestl256ByteCompression,
			HasherChallenger<Groestl256>,
			_,
		>(&constraint_system, args.log_inv_rate as usize, SECURITY_BITS, &[], witness, &backend)?;

	println!("Proof size: {}", ByteSize::b(proof.get_proof_size() as u64));

	constraint_system::verify::<
		U,
		CanonicalTowerFamily,
		Groestl256,
		Groestl256ByteCompression,
		HasherChallenger<Groestl256>,
	>(&constraint_system, args.log_inv_rate as usize, SECURITY_BITS, &[], proof)?;

	Ok(())
}

// The output is wrapped in a Result to allow matching on errors.
// Returns an Iterator to the Reader of the lines of the file.
fn read_lines<P>(filename: P) -> io::Result<io::Lines<io::BufReader<File>>>
where
	P: AsRef<Path>,
{
	let file = File::open(filename)?;
	Ok(io::BufReader::new(file).lines())
}
