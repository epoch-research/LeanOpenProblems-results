import FormalConjectures.Util.ProblemImports

lemma padicValNat_le_two_mul_sqrt (x : ℕ) : padicValNat 2 x ≤ 2 * Nat.sqrt x := sorry

lemma padicValInt_le_two_mul_sqrt (y : ℤ) : padicValInt 2 y ≤ 2 * Nat.sqrt y.natAbs := by
  unfold padicValInt
  exact padicValNat_le_two_mul_sqrt y.natAbs
