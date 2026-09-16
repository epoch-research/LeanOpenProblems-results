import Mathlib
import Mathlib.Data.Nat.Factors

open Nat List

lemma factors_getLast (m : ℕ) (hm : 1 < m) : ∃ p, p ∈ m.primeFactorsList ∧ ∀ q ∈ m.primeFactorsList, q ≤ p := by
  sorry
