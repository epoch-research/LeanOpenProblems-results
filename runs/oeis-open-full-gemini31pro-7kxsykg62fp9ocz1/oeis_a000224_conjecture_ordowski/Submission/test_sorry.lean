import Mathlib

lemma test {F : Type*} [Field F] [Fintype F] [DecidableEq F] (hF : ringChar F ≠ 2) (a : F) (S : Finset F) (ha : a ∉ S) :
  ({x : F | x ^ 2 = a}.toFinset = ∅) := by
  ext x
  simp
  intro hx
  apply ha
  sorry
