import FormalConjectures.Util.ProblemImports

lemma k_sq_div_piecewise_strong (n k : ℕ) (hn : 5 ≤ n) (hk : k < n) : k^2 / n ≥ if 3 * k ≥ n + 1 then k - (n + 1) / 3 else 0 := by
  split_ifs with h
  · have hk_sub : k ≥ (n + 1) / 3 := by omega
    have h_int : ((k^2 / n : ℕ) : ℤ) ≥ (k : ℤ) - (((n + 1) / 3 : ℕ) : ℤ) := by
      have h_div : ((k^2 : ℕ) : ℤ) = (n : ℤ) * ((k^2 / n : ℕ) : ℤ) + ((k^2 % n : ℕ) : ℤ) := by
        exact_mod_cast (Nat.div_add_mod (k^2) n).symm
      have h_div2 : ((n + 1 : ℕ) : ℤ) = 3 * (((n + 1) / 3 : ℕ) : ℤ) + (((n + 1) % 3 : ℕ) : ℤ) := by
        exact_mod_cast (Nat.div_add_mod (n + 1) 3).symm
      have h_mod_lt : ((k^2 % n : ℕ) : ℤ) < (n : ℤ) := by exact_mod_cast Nat.mod_lt _ (by omega)
      have h_mod_lt2 : (((n + 1) % 3 : ℕ) : ℤ) < 3 := by exact_mod_cast Nat.mod_lt _ (by omega)
      by_contra h_lt
      push_neg at h_lt
      have h_mul_lt : (n : ℤ) * ((k^2 / n : ℕ) : ℤ) ≤ (n : ℤ) * ((k : ℤ) - (((n + 1) / 3 : ℕ) : ℤ) - 1) := by
        nlinarith
      nlinarith
    exact_mod_cast h_int
  · omega
