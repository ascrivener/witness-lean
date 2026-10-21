import Mathlib.Data.Nat.Prime.Defs

/-- The bounty: there are infinitely many primes. -/
def GoalPrimes : Prop := ∀ n : ℕ, ∃ p, n ≤ p ∧ Nat.Prime p
