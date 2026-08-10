import FormalConjectures.Util.ProblemImports

lemma k_bound_universal_strongest (n k : ℕ) (hn : 5 ≤ n) (hk : k < n) : 3 * (k^2 / n) + 3 * ((n + 1) / 3) ≥ 3 * k := sorry

lemma k_sq_div_piecewise_strong (n k : ℕ) (hn : 5 ≤ n) (hk : k < n) : k^2 / n ≥ if 3 * k ≥ n + 1 then k - (n + 1) / 3 else 0 := by
  have h_univ := k_bound_universal_strongest n k hn hk
  split_ifs with h
  · omega
  · omega
