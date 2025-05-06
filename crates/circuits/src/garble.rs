use binius_core::oracle::OracleId;
use binius_field::BinaryField32b;
use binius_macros::arith_expr;
use rand::Rng;

use crate::{
	blake3::Blake3CompressState, builder::ConstraintSystemBuilder, unconstrained::fixed_u32,
};

/// A 128-bit label for a wire
#[derive(Debug, Copy, Clone)]
pub struct Label {
	idx: usize,
	label: [u32; 4],
}

#[derive(Debug, Copy, Clone)]
pub struct WitnessedLabel {
	_idx: usize,
	label: [OracleId; 4],
}

impl Label {
	pub fn random(idx: usize, rng: &mut impl Rng) -> Self {
		let label = [rng.gen(), rng.gen(), rng.gen(), rng.gen()];
		Self { idx, label }
	}

	pub fn witness(&self, builder: &mut ConstraintSystemBuilder) -> WitnessedLabel {
		let label = self
			.label
			.iter()
			.map(|value| fixed_u32::<BinaryField32b>(builder, "", 0, vec![*value]).unwrap())
			.collect::<Vec<_>>()
			.try_into()
			.unwrap();
		WitnessedLabel {
			_idx: self.idx,
			label,
		}
	}
}

/// A 128-bit output in a garbling table
#[derive(Debug, Copy, Clone)]
pub struct Output(Blake3CompressState, [u32; 4]);

#[derive(Debug, Copy, Clone)]
pub struct WitnessedOutput(Blake3CompressState, [OracleId; 4]);

impl Output {
	pub fn witness(&self, builder: &mut ConstraintSystemBuilder) -> WitnessedOutput {
		WitnessedOutput(
			self.0,
			self.1
				.iter()
				.map(|value| fixed_u32::<BinaryField32b>(builder, "", 0, vec![*value]).unwrap())
				.collect::<Vec<_>>()
				.try_into()
				.unwrap(),
		)
	}
}

/// A gate with left, right, and output wires
#[derive(Debug, Copy, Clone)]
pub struct Gate {
	pub left: (Label, Label),
	pub right: (Label, Label),
	pub out: (Label, Label),
}

impl Gate {
	/// Generate wire labels for a gate
	#[allow(dead_code)]
	pub fn generate_labels(left: usize, right: usize, out: usize, rng: &mut impl Rng) -> Self {
		let left = (Label::random(left, rng), Label::random(left, rng));
		let right = (Label::random(right, rng), Label::random(right, rng));
		let out = (Label::random(out, rng), Label::random(out, rng));

		Self { left, right, out }
	}

	/// Garble the output values of an AND gate
	///
	/// Left | Right | Out
	///   0  |   0   |  0
	///   0  |   1   |  0
	///   1  |   0   |  0
	///   1  |   1   |  1
	pub fn garble_and_gate(&self, rng: &mut impl Rng) -> [Output; 4] {
		// hash(left, right) XOR out
		let mut generate_output = |left: Label, right: Label, out: Label| -> Output {
			let hash_left_right: (Blake3CompressState, [u32; 4]) = {
				let mut input: [u32; 16] = [0; 16];
				for (idx, word) in left.label.iter().chain(right.label.iter()).enumerate() {
					input[idx] = *word;
				}
				let state = Blake3CompressState::random(input, rng);

				(state, state.compress()[..4].try_into().unwrap())
			};

			Output(
				hash_left_right.0,
				hash_left_right
					.1
					.iter()
					.zip(out.label.iter())
					.map(|(hash, out)| hash ^ out)
					.collect::<Vec<_>>()
					.try_into()
					.unwrap(),
			)
		};

		let output_0 = generate_output(self.left.0, self.right.0, self.out.0);
		let output_1 = generate_output(self.left.0, self.right.1, self.out.0);
		let output_2 = generate_output(self.left.1, self.right.0, self.out.0);
		let output_3 = generate_output(self.left.1, self.right.1, self.out.1);

		[output_0, output_1, output_2, output_3]
	}

	#[allow(dead_code)]
	pub fn witness(
		&self,
		builder: &mut ConstraintSystemBuilder<'_>,
		rng: &mut impl Rng,
	) -> WitnessedGate {
		let out = (self.out.0.witness(builder), self.out.1.witness(builder));
		let output = self.garble_and_gate(rng);
		let output = output
			.iter()
			.map(|output| output.witness(builder))
			.collect::<Vec<_>>()
			.try_into()
			.unwrap();

		WitnessedGate { out, output }
	}
}

#[derive(Debug, Copy, Clone)]
pub struct WitnessedGate {
	pub out: (WitnessedLabel, WitnessedLabel),
	pub output: [WitnessedOutput; 4],
}

impl WitnessedGate {
	/// Garble the output values of an AND gate in-circuit
	///
	/// Left | Right | Out
	///   0  |   0   |  0
	///   0  |   1   |  0
	///   1  |   0   |  0
	///   1  |   1   |  1
	pub fn garble_and_gate(
		&self,
		builder: &mut ConstraintSystemBuilder<'_>,
	) -> Result<(), anyhow::Error> {
		let mut table_row = |row: usize| -> Result<(), anyhow::Error> {
			let hash_input_labels =
				crate::blake3::blake3_compress(builder, &Some(vec![self.output[row].0]), 1)?.output;
			let output_wire_label = match row {
				0 => self.out.0.label,
				1 => self.out.0.label,
				2 => self.out.0.label,
				3 => self.out.1.label,
				_ => unimplemented!(),
			};

			for byte in 0..4 {
				builder.assert_zero(
					"b32_add",
					[
						hash_input_labels[byte],
						output_wire_label[byte],
						self.output[row].1[byte],
					],
					arith_expr!(
						[hash_input_labels, output_wire_label, output] =
							hash_input_labels + output_wire_label - output
					)
					.convert_field(),
				);
			}

			Ok(())
		};

		table_row(0)?;
		table_row(1)?;
		table_row(2)?;
		table_row(3)?;

		Ok(())
	}
}
