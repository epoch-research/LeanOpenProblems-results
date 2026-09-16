import Mathlib
open Finset

theorem div_eq_filter (n : ℕ) : Nat.divisors n = (Ico 1 (n+1)).filter (· ∣ n) := by exact?
