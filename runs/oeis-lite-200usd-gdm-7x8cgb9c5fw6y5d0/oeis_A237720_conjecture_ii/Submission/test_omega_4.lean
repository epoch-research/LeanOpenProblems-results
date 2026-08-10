import FormalConjectures.Util.ProblemImports

open Nat

lemma sqrt_succ_eq_sqrt_of_not_sq (x : ℕ) (hnot : x + 1 ≠ (sqrt (x + 1)) * (sqrt (x + 1))) : sqrt (x + 1) = sqrt x := by
  have h1 : sqrt x * sqrt x ≤ x := sqrt_le x
  have h2 : x < (sqrt x + 1) * (sqrt x + 1) := lt_succ_sqrt x
  have h3 : x + 1 ≤ (sqrt x + 1) * (sqrt x + 1) := by omega
  have h4 : x + 1 < (sqrt x + 1) * (sqrt x + 1) := by
    by_contra hc
    have hc' : x + 1 = (sqrt x + 1) * (sqrt x + 1) := by omega
    have h_sq : x + 1 = sqrt (x + 1) * sqrt (x + 1) := by
      have : sqrt (x + 1) = sqrt x + 1 := by
        rw [hc']
        exact sqrt_eq (sqrt x + 1)
      rw [this, ← hc']
    exact hnot h_sq
  have h5 : sqrt x * sqrt x ≤ x + 1 := by omega
  exact (eq_sqrt.mpr ⟨h5, h4⟩).symm

theorem test_hn_sq_f (n p S : ℕ) (hS_ge2 : S ≥ 2) (h_sqrt_eq : sqrt (n + p) = S - 1)
    (hc_sq : n + p ≠ sqrt (n + p) * sqrt (n + p)) : n + 1 + p ≠ S * S := by
  intro hc_sq_succ
  have h_sqrt_succ_eq : sqrt (n + p + 1) = sqrt (n + p) := sqrt_succ_eq_sqrt_of_not_sq (n + p) hc_sq
  have h_sqrt_succ_S : sqrt (n + p + 1) = S := by
    have : n + p + 1 = S * S := by omega
    rw [this]
    exact sqrt_eq S
  omega
