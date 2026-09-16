

lemma composite_A000224_bound2 {n : ℕ} (h_comp : ¬ n.Prime) (hn : 1 < n) (h_odd : Odd n) :
  A000224 n ≤ (n - 1) / 2 := by
  have h_min_fac : n.minFac ∣ n := Nat.minFac_dvd n
  have h_min_fac_prime : n.minFac.Prime := Nat.minFac_prime (by omega)
  have h_min_fac_ne_n : n.minFac ≠ n := by
    intro h_eq
    rw [← h_eq] at h_comp
    exact h_comp h_min_fac_prime
  have h_n_pos : 0 < n := by omega
  have hn_eq : n = n.minFac * (n / n.minFac) := (Nat.mul_div_cancel' h_min_fac).symm
  let p := n.minFac
  let q := n / n.minFac
  have hpq : n = p * q := hn_eq
  have h_p_ge_3 : 3 ≤ p := by
    have h_p_ne_2 : p ≠ 2 := by
      intro hp2
      have H_dvd : 2 ∣ n := by
        change p = 2 at hp2
        rw [←hp2]
        exact h_min_fac
      have H : n % 2 = 0 := Nat.mod_eq_zero_of_dvd H_dvd
      have H2 : n % 2 = 1 := by
        obtain ⟨x, hx⟩ := h_odd
        rw [hx]
        have h_mod : (1 + 2 * x) % 2 = 1 % 2 := Nat.add_mul_mod_self_left 1 2 x
        have H_add : 2 * x + 1 = 1 + 2 * x := add_comm _ _
        rw [H_add, h_mod]
      rw [H2] at H
      contradiction
    have h_p_ge_2 : 2 ≤ p := h_min_fac_prime.two_le
    omega
  have h_q_ge_3 : 3 ≤ q := by
    have hpq_pos : 0 < p * q := by omega
    have hq_pos : 0 < q := by nlinarith
    have h_q_ne_1 : q ≠ 1 := by
      intro hq1
      have H : n = p := by
        calc n = p * q := hpq
          _ = p * 1 := by rw [hq1]
          _ = p := mul_one p
      exact h_min_fac_ne_n H.symm
    have h_q_ne_2 : q ≠ 2 := by
      intro hq2
      have H_dvd : 2 ∣ n := by
        rw [hpq, hq2]
        exact dvd_mul_left 2 p
      have H : n % 2 = 0 := Nat.mod_eq_zero_of_dvd H_dvd
      have H2 : n % 2 = 1 := by
        obtain ⟨x, hx⟩ := h_odd
        rw [hx]
        have h_mod : (1 + 2 * x) % 2 = 1 % 2 := Nat.add_mul_mod_self_left 1 2 x
        have H_add : 2 * x + 1 = 1 + 2 * x := add_comm _ _
        rw [H_add, h_mod]
      rw [H2] at H
      contradiction
    omega
  exact composite_A000224_bound hpq h_p_ge_3 h_q_ge_3 h_odd
