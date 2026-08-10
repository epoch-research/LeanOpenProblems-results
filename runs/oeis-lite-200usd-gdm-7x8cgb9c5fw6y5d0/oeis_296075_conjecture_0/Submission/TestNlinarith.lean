import FormalConjectures.Util.ProblemImports

theorem test_strong_nlinarith (n : ℕ) (hn12 : n > 12) (S : ℤ) (h_abund : S ≥ 2 * (n : ℤ) + 3)
    (h_le : (n : ℤ) * (2 * S - 1) ≤ S * S - 2 * S + 2 * (n : ℤ) + 1) : False := by
  let k : ℤ := S - 2 * (n : ℤ) - 3
  have hk : k ≥ 0 := by omega
  have hS : S = 2 * (n : ℤ) + 3 + k := by omega
  have h_eq : S * S - 2 * (n : ℤ) * S - 2 * S + 3 * (n : ℤ) + 1 = 5 * (n : ℤ) + 4 + k * (2 * (n : ℤ) + 4) + k * k := by
    rw [hS]
    ring
  have h_k_nonneg : k * (2 * (n : ℤ) + 4) ≥ 0 := by
    apply mul_nonneg hk (by omega)
  have h_kk_nonneg : k * k ≥ 0 := by
    apply mul_self_nonneg
  have h_le_rewritten : (n : ℤ) * 2 * S - (n : ℤ) ≤ S * S - 2 * S + 2 * (n : ℤ) + 1 := by
    calc
      (n : ℤ) * 2 * S - (n : ℤ) = (n : ℤ) * (2 * S - 1) := by ring
      _ ≤ S * S - 2 * S + 2 * (n : ℤ) + 1 := h_le
  have h_final : S * S - (n : ℤ) * 2 * S - 2 * S + 3 * (n : ℤ) + 1 ≤ 0 := by
    linarith [h_le_rewritten]
  have h_final' : S * S - 2 * (n : ℤ) * S - 2 * S + 3 * (n : ℤ) + 1 ≤ 0 := by
    have : (n : ℤ) * 2 * S = 2 * (n : ℤ) * S := by ring
    omega
  rw [h_eq] at h_final'
  omega
