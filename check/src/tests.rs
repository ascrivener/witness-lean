use super::*;
use witness_types::{CheckBlob, CheckMode, check_args};

fn run(mode: CheckMode, blobs: &[(bool, &[u8])], params: &[u8], witness: &[u8]) -> bool {
	let blobs: Vec<_> = blobs.iter().map(|&(trusted, data)| CheckBlob { trusted, hash: [0; 32], data }).collect();
	let args = check_args(mode, &blobs, params, witness);
	// Type errors panic, which the PVM turns into false.
	std::panic::catch_unwind(|| check(&Input::parse(&args).unwrap())).unwrap_or(false)
}

#[test]
fn reveal_params_name_a_statement_and_a_theorem() {
	assert_eq!(names(b"Goal\ngoal"), Some(("Goal", "goal")));
	assert_eq!(names(b"Goal"), None);
	assert_eq!(names(b"\ngoal"), None);
	assert_eq!(names(b"Goal\n"), None);
	assert_eq!(names(b"\xff\ngoal"), None);
}

#[test]
fn attest_mode_shape() {
	let empty: &[u8] = include_bytes!("../../vendor/nanoda/test_resources/Empty/export");
	// An empty layer adds nothing to check, so it attests, as a root or after a trusted chain.
	assert!(run(CheckMode::Attest, &[(false, empty)], b"", b""));
	assert!(run(CheckMode::Attest, &[(true, empty), (false, empty)], b"", b""));
	assert!(!run(CheckMode::Attest, &[(false, empty)], b"params", b""), "params must be empty");
	assert!(!run(CheckMode::Attest, &[(false, empty), (false, empty)], b"", b""), "an untrusted chain");
	assert!(!run(CheckMode::Attest, &[], b"", b""), "no subject");
	assert!(!run(CheckMode::Attest, &[(false, b"not an export")], b"", b""));
}

macro_rules! fixture {
	($name: literal) => {
		include_bytes!(concat!("../testdata/", $name, ".bin")).as_slice()
	};
}

/// GoalTwo's environment, in three layers.
const TWO: [&[u8]; 3] = [fixture!("env-two-layer-0"), fixture!("env-two-layer-1"), fixture!("env-two-layer-2")];

/// Reveal `delta` for `statement` and `theorem` on `layers`, the first `trusted` of them trusted.
fn reveal_on(layers: &[&[u8]], trusted: usize, names: &str, delta: &[u8]) -> bool {
	let blobs: Vec<(bool, &[u8])> = layers.iter().enumerate().map(|(i, l)| (i < trusted, *l)).collect();
	run(CheckMode::Reveal, &blobs, names.as_bytes(), delta)
}

#[test]
fn honest_proofs_are_accepted() {
	for trusted in 0..=3 {
		assert!(reveal_on(&TWO, trusted, "GoalTwo\ngoal_two", fixture!("delta-goal_two")), "{trusted} trusted");
	}
	assert!(reveal_on(&[fixture!("env-f")], 0, "GoalF\ngoal_f", fixture!("delta-goal_f")));
}

#[test]
fn attacks_are_rejected() {
	let two = |names: &str, delta| reveal_on(&TWO, 3, names, delta);
	assert!(!two("GoalTwo\ngoal_wrong", fixture!("delta-goal_wrong")), "proves True instead");
	assert!(!two("GoalTwo\ngoal_def", fixture!("delta-goal_def")), "a def, not a theorem");
	assert!(!two("GoalTwo\ngoal_two_axiom", fixture!("delta-goal_two_axiom")), "an extra axiom");
	assert!(!two("GoalTwo\ngoal_two_sorry", fixture!("delta-goal_two_sorry")), "sorry");
	assert!(!two("GoalTwo\nnonexistent", fixture!("delta-goal_two")), "no such theorem");
	assert!(!two("Nat.add\ngoal_two", fixture!("delta-goal_two")), "statement not a Prop definition");
	let f = [fixture!("env-f")];
	assert!(!reveal_on(&f, 1, "GoalF\ngoal_f", fixture!("delta-redefine")), "redefines myF");
	assert!(!reveal_on(&f, 1, "GoalF\ngoal_f", fixture!("delta-goal_two")), "a delta for another environment");
	assert!(!reveal_on(&TWO, 3, "GoalTwo\ngoal_two", b""), "no proof");
}

#[test]
fn proofs_are_type_checked() {
	// GoalTwo's last layer edited to say 2 + 2 = 5. It's a fine definition, so it attests, but the
	// honest proof (rfl) of 2 + 2 = 4 no longer type-checks against it, trusted or not.
	let five = [TWO[0], TWO[1], fixture!("env-five-layer-2")];
	assert!(run(CheckMode::Attest, &[(true, five[0]), (true, five[1]), (false, five[2])], b"", b""));
	for trusted in [0, 3] {
		assert!(!reveal_on(&five, trusted, "GoalTwo\ngoal_two", fixture!("delta-goal_two")), "{trusted} trusted");
	}
}

#[test]
fn layers_attest_one_after_another() {
	let attest = |layers: &[&[u8]]| {
		let (subject, chain) = layers.split_last().unwrap();
		let mut blobs: Vec<(bool, &[u8])> = chain.iter().map(|l| (true, *l)).collect();
		blobs.push((false, subject));
		run(CheckMode::Attest, &blobs, b"", b"")
	};
	assert!(attest(&TWO[..1]));
	assert!(attest(&TWO[..2]));
	assert!(attest(&TWO));
	// A layer only parses after the layers it was cut from.
	assert!(!attest(&[TWO[1]]), "without its chain");
	assert!(!attest(&[TWO[0], TWO[2]]), "a layer skipped");
	assert!(!attest(&[TWO[1], TWO[0]]), "out of order");
	// A layer that redeclares an earlier name doesn't parse either.
	assert!(!attest(&[TWO[0], TWO[1], TWO[2], TWO[2]]));
}
