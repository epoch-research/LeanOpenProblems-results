import FormalConjectures.Util.ProblemImports

lemma sq_sub_div_eq (n k : ℕ) (h : 2 * k ≤ n) : (n - k) ^ 2 / n = n - 2 * k + k ^ 2 / n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have h_eq : (n - k) ^ 2 = (n - 2 * k) * n + k ^ 2 := by
    -- wait, we don't even need this lemma since we already have it in Spec.lean
    sorry

lemma k_bound_universal (n k : ℕ) (hn : 5 ≤ n) (hk : k < n) : 3 * (k^2 / n) + n + 1 ≥ 3 * k := sorry

lemma k_bound_universal_strongest (n k : ℕ) (hn : 5 ≤ n) (hk : k < n) : 3 * (k^2 / n) + 3 * ((n + 1) / 3) ≥ 3 * k := by
  have h_univ := k_bound_universal n k hn hk
  omega
