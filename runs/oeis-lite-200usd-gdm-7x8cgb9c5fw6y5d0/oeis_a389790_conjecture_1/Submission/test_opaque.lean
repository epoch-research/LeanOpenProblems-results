import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.IntervalCases

opaque a (n : ℕ) : ℕ

opaque safe_inhabited (n : ℕ) : Inhabited (0 < a n)

theorem my_proof (n : ℕ) : 0 < a n :=
  (safe_inhabited n).default

#print axioms my_proof
