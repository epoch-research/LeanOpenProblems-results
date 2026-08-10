import FormalConjectures.Util.ProblemImports

lemma k_sq_div_piecewise_strong (n k : ℕ) (hn : 5 ≤ n) (hk : k < n) : k^2 / n ≥ if 3 * k ≥ n + 1 then k - (n + 1) / 3 else 0 := by
  split_ifs with h
  · have h_div : k^2 = n * (k^2 / n) + k^2 % n := (Nat.div_add_mod (k^2) n).symm
    have h_mod_lt : k^2 % n < n := Nat.mod_lt _ (by omega)
    have : (n + 1) / 3 ≥ 1 := by omega
    have h_div2 : (n + 1) = 3 * ((n + 1) / 3) + (n + 1) % 3 := (Nat.div_add_mod (n + 1) 3).symm
    have h_mod_lt2 : (n + 1) % 3 < 3 := Nat.mod_lt _ (by omega)
    by_contra h_lt
    push_neg at h_lt
    have h_mul : n * (k^2 / n + 1) ≤ n * (k - (n + 1) / 3) := Nat.mul_le_mul_left n h_lt
    have h_dist1 : n * (k^2 / n + 1) = n * (k^2 / n) + n := by ring
    have h_dist2 : n * (k - (n + 1) / 3) = n * k - n * ((n + 1) / 3) := by
      rw [Nat.mul_sub_left_distrib]
    rw [h_dist1, h_dist2] at h_mul
    have h_comb : k^2 + n ≤ n * k - n * ((n + 1) / 3) + k^2 % n := by omega
    have h_sub3 : n * ((n + 1) / 3) * 3 ≥ n * (n - 1) := by
      calc n * ((n + 1) / 3) * 3 = n * (3 * ((n + 1) / 3)) := by ring
      _ = n * (n + 1 - (n + 1) % 3) := by omega
      _ ≥ n * (n - 1) := by omega
    nlinarith
  · omega
