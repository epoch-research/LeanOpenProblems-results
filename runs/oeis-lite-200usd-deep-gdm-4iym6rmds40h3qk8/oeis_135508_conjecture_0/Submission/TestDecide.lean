import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 10000000

lemma prime_le_of_sq_le {q : ℕ} (hq : Nat.Prime q) (h : q * q ≤ 13588) : q ≤ 113 := by
  by_contra h_gt
  have hq_ge : q ≥ 114 := by omega
  have h_le_116 : q ≤ 116 := by
    by_contra h_gt2
    have : q ≥ 117 := by omega
    have : q * q ≥ 117 * 117 := by nlinarith
    omega
  interval_cases q
  · have : ¬ Nat.Prime 114 := by decide
    contradiction
  · have : ¬ Nat.Prime 115 := by decide
    contradiction
  · have : ¬ Nat.Prime 116 := by decide
    contradiction


