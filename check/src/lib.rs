//! A witness check for Lean 4 proofs, using [nanoda](../vendor/nanoda/VENDORED.md) as the
//! kernel.
//!
//! Every blob, and the witness, is a layer of one lean4export export (NDJSON or the binary
//! format): each continues the numbering of the layers before it.
//!
//! - **Attest mode:** the subject is a layer, and the chain before it is the layers it follows.
//!   Type-check the subject's declarations, trusting the chain's. Params must be empty. A library
//!   is attested this way layer by layer, each layer once.
//! - **Reveal mode:** params are `statement` and `theorem`, the names of a `Prop`-valued
//!   definition in the blobs and of the solver's theorem, separated by a newline. The witness is
//!   the solver's delta: the last layer, adding the proof. Bind the theorem to the statement (see
//!   `nanoda_lib::binding`), then type-check every untrusted layer and the delta.
//!
//! Only `propext`, `Classical.choice` and `Quot.sound` may be used as axioms, in any layer. Type
//! errors panic, which counts as false.

#![cfg_attr(not(test), no_std)]

extern crate alloc;

use alloc::vec::Vec;
use witness_check::{Input, Mode};

// nanoda recurses deeply while type checking. A 1 MiB stack sufficed for every proof the spike
// measured; natively it asks for 16 MiB for deep ones.
#[cfg(any(target_arch = "riscv32", target_arch = "riscv64"))]
polkavm_derive::min_stack_size!(8 * 1024 * 1024);

/// The statement and theorem names in reveal params.
fn names(params: &[u8]) -> Option<(&str, &str)> {
	let params = core::str::from_utf8(params).ok()?;
	let (statement, theorem) = params.split_once('\n')?;
	(!statement.is_empty() && !theorem.is_empty()).then_some((statement, theorem))
}

fn attest(input: &Input) -> bool {
	let Some(subject) = input.subject() else { return false };
	let parts: Vec<&[u8]> = input.blobs().map(|b| b.data).collect();
	// The service passes the chain trusted and the subject untrusted; nothing else is valid.
	let chain = input.blobs().take(parts.len() - 1);
	if !input.params.is_empty() || subject.trusted || chain.clone().any(|b| !b.trusted) {
		return false;
	}
	let Ok(layers) = nanoda_lib::binding::parse(&parts) else { return false };
	layers.check(layers.layer(layers.len() - 1));
	true
}

fn reveal(input: &Input) -> bool {
	let Some((statement, theorem)) = names(input.params) else { return false };
	let mut parts: Vec<&[u8]> = input.blobs().map(|b| b.data).collect();
	parts.push(input.witness);
	let Ok(layers) = nanoda_lib::binding::parse(&parts) else { return false };
	let delta = layers.len() - 1;
	let environment = layers.layers(0..delta);
	if layers.check_binding(statement, environment, theorem, layers.layer(delta)).is_err() {
		return false;
	}
	for (i, blob) in input.blobs().enumerate() {
		if !blob.trusted {
			layers.check(layers.layer(i));
		}
	}
	layers.check(layers.layer(delta));
	true
}

/// The check, for running natively too (see `tools/lean-host`).
pub fn check(input: &Input) -> bool {
	match input.mode {
		Mode::Attest => attest(input),
		Mode::Reveal => reveal(input),
	}
}

witness_check::declare_full_check!(check);

#[cfg(test)]
mod tests;
