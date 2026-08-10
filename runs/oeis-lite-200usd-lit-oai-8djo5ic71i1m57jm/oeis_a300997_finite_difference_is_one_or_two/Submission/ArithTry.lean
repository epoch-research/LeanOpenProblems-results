import FormalConjectures.Util.ProblemImports
lemma ceil_sub_identity {N a b : ℕ} (ha : a ≤ N) (hb : b ≤ N) :
    ((N - a) + (N - b) + 1) / 2 = N - (a + b) / 2 := by
  apply le_antisymm
  · rw [Nat.div_le_iff_le_mul_add_pred (by decide : 0 < 2)]
    have hq2 : 2 * ((a+b)/2) ≤ a+b := Nat.mul_div_le (a+b) 2
    omega
  · rw [Nat.le_div_iff_mul_le (by decide : 0 < 2)]
    have hle : a+b ≤ 2 * ((a+b)/2) + 1 := by
      rw [← Nat.div_le_iff_le_mul_add_pred (by decide : 0 < 2)]
    omega
