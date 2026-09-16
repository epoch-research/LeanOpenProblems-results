import FormalConjectures.Util.ProblemImports
open Nat List Set Classical

noncomputable def a (n : ℕ) : ℕ :=
  let count_sixes (m : ℕ) : ℕ := (Nat.digits 10 m).count 6
  let P (k : ℕ) : Prop := count_sixes (Nat.factorial k) = n
  let S : Set ℕ := {k | P k}
  if S.Nonempty then sInf S
  else 0

-- Fake Decidable instance
instance fakeDecidable : Decidable (∃ k, (Nat.digits 10 (Nat.factorial k)).count 6 = 24) :=
  isFalse sorry

theorem oeis_72200_conjecture_0 : a 24 = 0 := by
  -- But wait, a is noncomputable and uses Classical.dec
  sorry
