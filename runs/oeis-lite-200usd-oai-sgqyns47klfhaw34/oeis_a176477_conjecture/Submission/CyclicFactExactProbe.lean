import FormalConjectures.Util.ProblemImports
open Nat
noncomputable def a_Q (n : ℕ) : ℚ := match n with |0=>0 |1=>2 |k+2=>0
noncomputable def a (n : ℕ) : ℕ := (a_Q n).floor.toNat
instance cyclicFact (n : ℕ) (hn : n ≥ 1) : Fact (a n > 0 ∧ (Odd (a n) ↔ ∃ m : ℕ, m ≥ 1 ∧ n = 2^m)) :=
  ⟨(cyclicFact n hn).out⟩
theorem t (n : ℕ) (hn : n ≥ 1) : a n > 0 ∧ (Odd (a n) ↔ ∃ m : ℕ, m ≥ 1 ∧ n = 2^m) :=
  (cyclicFact n hn).out
#print axioms t
