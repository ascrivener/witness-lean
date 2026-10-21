import Mathlib.Data.Nat.Prime.Infinite
import Primes.Statement

theorem goal_primes : GoalPrimes := fun n => Nat.exists_infinite_primes n
