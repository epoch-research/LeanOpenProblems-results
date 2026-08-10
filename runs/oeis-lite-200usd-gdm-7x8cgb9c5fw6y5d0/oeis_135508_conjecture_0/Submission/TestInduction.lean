import FormalConjectures.Util.ProblemImports

open Nat

lemma divisor_mod_r_eq (r : ℕ) (hr_ge : r ≥ 5) (hr : Nat.Prime r) (k : ℕ) (hk : k ∣ r^2 - 2) (j : ℕ) (hk_eq : k + 2 = j * r) : k = r^2 - 2 := by
  rcases hk with ⟨m, hm⟩
  have hk_pos : k > 0 := by
    by_contra h_zero
    have : k = 0 := by omega
    rw [this] at hm
    simp at hm
    have : r^2 ≥ 25 := by nlinarith
    omega
  have hj_pos : j ≥ 1 := by
    by_contra h_zero
    have : j = 0 := by omega
    rw [this] at hk_eq
    simp at hk_eq
  have h_jr_ge : j * r ≥ 2 := by nlinarith
  have h_k_eq : k = j * r - 2 := by omega
  have h_sub_eq : r^2 - 2 = (j * r - 2) * m := by
    rw [hm, h_k_eq]
  have h_mul_sub : (j * r - 2) * m = j * r * m - 2 * m := by
    have := Nat.mul_sub_right_distrib (j * r) 2 m
    have h_assoc : (j * r) * m = j * r * m := by ring
    rw [h_assoc] at this
    exact this
  rw [h_mul_sub] at h_sub_eq
  have hm_pos : m > 0 := by
    by_contra h
    have : m = 0 := by omega
    subst this
    simp at hm
    have : r^2 ≥ 25 := by nlinarith
    omega
  have h_m_eq : m = 1 ∨ m > 1 := by
    rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hm_pos) with h_eq | h_lt
    · left; exact h_eq.symm
    · right; exact h_lt
  rcases h_m_eq with rfl | hm_gt
  · simp at hm
    exact hm.symm
  · have h_ge : j * r * m ≥ 2 * m := by nlinarith
    have h_sub_eq2 : r^2 - 2 + 2 * m = j * r * m := by omega
    have h_div : r ∣ 2 * m - 2 := by
      use j * m - r
      have h_dist : r * (j * m - r) = r * (j * m) - r * r := Nat.mul_sub_left_distrib r (j * m) r
      have h_r2 : r * r = r^2 := by ring
      rw [h_r2] at h_dist
      have h_sub_eq3 : r * (j * m) = r^2 - 2 + 2 * m := by
        have : r * (j * m) = j * r * m := by ring
        omega
      have h_ge2 : r * (j * m) ≥ r^2 := by
        have : r * (j * m) = j * r * m := by ring
        omega
      have h_sub_eq4 : r * (j * m) - r^2 = 2 * m - 2 := by
        rw [h_sub_eq3]
        have : r^2 ≥ 25 := by nlinarith
        omega
      rw [h_dist, h_sub_eq4]
    have h_coprime : Nat.Coprime r 2 := by
      have h_cases : Nat.gcd r 2 = 1 ∨ Nat.gcd r 2 = 2 := by
        have h_gcd_le : Nat.gcd r 2 ≤ 2 := Nat.le_of_dvd (by decide) (Nat.gcd_dvd_right r 2)
        have h_gcd_pos : Nat.gcd r 2 > 0 := Nat.gcd_pos_of_pos_right r (by decide)
        omega
      rcases h_cases with h_gcd1 | h_gcd2
      · exact h_gcd1
      · have h_dvd_left := Nat.gcd_dvd_left r 2
        rw [h_gcd2] at h_dvd_left
        have h_eq : 2 = 1 ∨ 2 = r := hr.eq_one_or_self_of_dvd 2 h_dvd_left
        omega
    have h_div_m1 : r ∣ m - 1 := by
      have h_div2 : r ∣ 2 * (m - 1) := by
        have : 2 * (m - 1) = 2 * m - 2 := by omega
        rw [this]
        exact h_div
      exact Nat.Coprime.dvd_of_dvd_mul_left h_coprime h_div2
    have h_le_m1 : r ≤ m - 1 := Nat.le_of_dvd (by omega) h_div_m1
    have h_m_ge : m ≥ r + 1 := by omega
    have hj_ge2 : j ≥ 2 := by
      by_contra h_lt
      have : j = 1 := by omega
      subst this
      have hk_eq2 : k + 2 = r := by omega
      have hk_dvd_r2 : k ∣ r^2 - 2 := ⟨m, hm⟩
      have h_sub : (r^2 - 2) - (r - 2) * (r + 2) = 2 := by
        have h_eq : r^2 = (r - 2) * (r + 2) + 4 := by
          have h_r : r = (r - 2) + 2 := by omega
          have h_pow2 : r^2 = r * r := by ring
          rw [h_pow2, h_r]
          have h_sim : (r - 2) + 2 - 2 = r - 2 := by omega
          rw [h_sim]
          ring
        omega
      have h_dvd_2 : k ∣ 2 := by
        have h_k_eq_sub : k = r - 2 := by omega
        have h_dvd_mul : k ∣ k * (r + 2) := dvd_mul_right k (r + 2)
        have h_eq_mul : k * (r + 2) = (r - 2) * (r + 2) := by rw [h_k_eq_sub]
        rw [h_eq_mul] at h_dvd_mul
        have hk_dvd_sub := Nat.dvd_sub hk_dvd_r2 h_dvd_mul
        rw [h_sub] at hk_dvd_sub
        exact hk_dvd_sub
      have h_le : k ≤ 2 := Nat.le_of_dvd (by omega) h_dvd_2
      have : r - 2 ≤ 2 := by omega
      omega
    have h_jr_ge2 : j * r ≥ 2 * r := Nat.mul_le_mul_right r hj_ge2
    have h_k_ge : k ≥ 2 * r - 2 := by omega
    have h_prod_ge : (2 * r - 2) * (r + 1) ≤ k * m := Nat.mul_le_mul h_k_ge h_m_ge
    have h_prod_val : (2 * r - 2) * (r + 1) = 2 * r^2 - 2 := by
      have h_dist : (2 * r - 2) * (r + 1) = 2 * r * (r + 1) - 2 * (r + 1) := Nat.mul_sub_right_distrib (2 * r) 2 (r + 1)
      have h1 : 2 * r * (r + 1) = 2 * r^2 + 2 * r := by
        have h_r2 : r^2 = r * r := by ring
        rw [h_r2]
        ring
      have h2 : 2 * (r + 1) = 2 * r + 2 := by ring
      rw [h1, h2] at h_dist
      omega
    have h_prod_eq : k * m = r^2 - 2 := hm.symm
    rw [h_prod_val, h_prod_eq] at h_prod_ge
    have : r^2 ≥ 25 := by nlinarith
    omega

lemma prime_dvd_x_seq_sq_sub_one_bounded_1019 (r : ℕ) (hr_le : r ≤ 1019) (hr : Nat.Prime r) : r ∣ x_seq (r^2 - 1) := sorry

lemma x_seq_pos (n : ℕ) (hn : n > 0) : x_seq n > 0 := sorry
lemma x_seq_dvd (n : ℕ) (hn : n > 0) : x_seq n ∣ x_seq (n + 1) := sorry
lemma x_seq_dvd_of_le (a b : ℕ) (ha : a > 0) (hab : a ≤ b) : x_seq a ∣ x_seq b := sorry
lemma x_seq_step_eq_gen (n : ℕ) (hn : n ≥ 2) : x_seq n = x_seq (n - 1) * (2 + n / Nat.gcd (x_seq (n - 1)) n) := sorry
lemma max_prime_factor_x_seq (n : ℕ) (hn : n > 0) (r : ℕ) (hr : Nat.Prime r) (hd : r ∣ x_seq n) : r ≤ n + 2 := sorry

lemma prime_dvd_x_seq_sq_sub_one (r : ℕ) (hr : Nat.Prime r) : r ∣ x_seq (r^2 - 1) := by
  induction' r using Nat.strong_induction_on with r ih
  by_cases h_le : r ≤ 1019
  · exact prime_dvd_x_seq_sq_sub_one_bounded_1019 r h_le hr
  · have hr_ge : r ≥ 5 := by omega
    have h_r2_sub_2_pos : r^2 - 2 > 0 := by
      have : r^2 ≥ 25 := by nlinarith
      omega
    have h_dvd : x_seq (r^2 - 2) ∣ x_seq (r^2 - 1) := by
      apply x_seq_dvd_of_le
      · exact h_r2_sub_2_pos
      · omega
    apply dvd_trans _ h_dvd
    set n := r^2 - 2
    have hn : n ≥ 2 := by
      have : r^2 ≥ 25 := by nlinarith
      omega
    have h_step := x_seq_step_eq_gen n hn
    set g := Nat.gcd (x_seq (n - 1)) n
    set k := n / g
    by_cases h_div_prev : r ∣ x_seq (n - 1)
    · have h_dvd2 : x_seq (n - 1) ∣ x_seq n := by
        have h_pos : n - 1 > 0 := by omega
        have h_eq : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
        rw [← h_eq]
        exact x_seq_dvd (n - 1) h_pos
      exact dvd_trans h_div_prev h_dvd2
    · have h_g_eq : g = 1 := by
        by_contra h_g_gt
        have h_g_gt1 : g > 1 := by omega
        set q := Nat.minFac g
        have hq_prime : Nat.Prime q := Nat.minFac_prime h_g_gt1
        have hq_dvd_g : q ∣ g := Nat.minFac_dvd g
        have hg_dvd_n : g ∣ n := Nat.gcd_dvd_right (x_seq (n - 1)) n
        have hg_dvd_x : g ∣ x_seq (n - 1) := Nat.gcd_dvd_left (x_seq (n - 1)) n
        have hq_dvd_n : q ∣ r^2 - 2 := dvd_trans hq_dvd_g hg_dvd_n
        have hq_dvd_x : q ∣ x_seq (r^2 - 3) := dvd_trans hq_dvd_g hg_dvd_x
        have hq_ne_r : q ≠ r := by
          intro h_eq
          rw [h_eq] at hq_dvd_n
          have h_div_2 : r ∣ 2 := by
            rcases hq_dvd_n with ⟨w, hw⟩
            have h_pow2 : r^2 = r * r := by ring
            omega
          have h_eq2 : r = 1 ∨ r = 2 := hr.eq_one_or_self_of_dvd 2 h_div_2
          omega
        by_cases h_q_lt : q < r
        · have h_q_dvd_sq : q ∣ x_seq (q^2 - 1) := ih q h_q_lt hq_prime
          have h_q2_sub_1_le : q^2 - 1 ≤ r^2 - 3 := by
            have : q ≤ r - 1 := by omega
            have : q^2 ≤ (r - 1)^2 := Nat.mul_le_mul this this
            have h_ring : (r - 1)^2 = r^2 - 2 * r + 1 := by
              have : r ≥ 1 := by omega
              omega
            omega
          have h_q2_sub_1_pos : q^2 - 1 > 0 := by
            have : q ≥ 2 := Nat.Prime.two_le hq_prime
            have : q^2 ≥ 4 := by nlinarith
            omega
          have h_x_dvd : x_seq (q^2 - 1) ∣ x_seq (r^2 - 3) := x_seq_dvd_of_le (q^2 - 1) (r^2 - 3) h_q2_sub_1_pos h_q2_sub_1_le
          have h_q_dvd_x' : q ∣ x_seq (r^2 - 3) := dvd_trans h_q_dvd_sq h_x_dvd
          -- We already have hq_dvd_x : q | x_seq (r^2 - 3). This is fine.
          -- Wait! We need a contradiction?
          -- Actually, we split on whether q < r or q > r.
          -- If q < r, then q is a prime factor of g. Why is this a contradiction?
          -- Ah, wait! If q < r, it is NOT a contradiction!
          -- But wait!
          -- If q < r is always true, then how do we get a contradiction?
          -- Ah!
          -- If q < r, we got q ∣ x_seq (r^2 - 3) and q ∣ r^2 - 2, which just means q ∣ g.
          -- This is not a contradiction.
          -- But wait!
          -- If g > 1, then we can write k = n / g.
          -- Since ¬ r ∣ x_seq (n-1), and r ∣ x_seq n.
          -- Wait, we wanted to show r ∣ x_seq n!
          -- But we cannot assume r ∣ x_seq n!
          -- Ah...
          -- If we can't assume r ∣ x_seq n, then we cannot use the fact that r ∣ 2 + k to get k + 2 = j * r!
          -- Yes! We need to prove r ∣ x_seq n!
          -- How do we prove r ∣ x_seq n?
          -- Is it by showing r ∣ 2 + k?
          -- Since k = n / g.
          -- Is k always of the form j * r - 2?
          -- If we can show g = 1, then k = r^2 - 2, so 2 + k = r^2, which is a multiple of r.
          -- But why is g = 1?
          -- If g > 1, then we have a prime factor q of g.
          -- If q < r, then q ∣ x_seq (r^2 - 3).
          -- If q > r, we showed it's impossible because m < r, so m has a prime factor q' < r, which divides g, so q' < q, contradiction.
          -- So indeed, ALL prime factors of g must be < r.
          -- But why is g > 1 impossible?
          -- Wait!
          -- Is g > 1 actually possible?
          -- Yes! For r = 11, g = 7 > 1!
          -- But for r = 11, we had r ∣ x_seq (r^2 - 3)!
          -- Ah!!!
          -- If r ∣ x_seq (r^2 - 3), we are in the h_div_prev case!
          -- Yes!
          -- So if ¬ r ∣ x_seq (r^2 - 3), then we must have g = 1!
          -- Why?
          -- Because if ¬ r ∣ x_seq (r^2 - 3), and g > 1.
          -- Since g > 1, all prime factors of g are < r.
          -- Let q < r be a prime factor of g.
          -- Since q < r, q ∣ x_seq (r^2 - 3) and q ∣ r^2 - 2.
          -- This is still consistent.
          -- Wait, why does ¬ r ∣ x_seq (r^2 - 3) imply g = 1?
          -- Let's think.
          -- If g > 1, then g ∣ r^2 - 2.
          -- Since ¬ r ∣ x_seq (r^2 - 3), and r is prime, r does not divide g.
          -- So g is coprime to r.
          -- But why must g be 1?
          -- Actually, is g always 1 when ¬ r ∣ x_seq (r^2 - 3)?
          -- Yes!
          -- But how can we prove this?
          -- Wait!
          -- If we cannot prove g = 1, is there a way to show r ∣ 2 + k?
          -- `2 + k = 2 + (r^2 - 2) / g`.
          -- Since g ∣ r^2 - 2, let r^2 - 2 = g * k.
          -- We want to show r ∣ 2 + k.
          -- This is equivalent to: k ≡ -2 (mod r).
          -- But we proved that the ONLY divisor k of r^2 - 2 with k ≡ -2 (mod r) is k = r^2 - 2 (corresponding to g = 1)!
          -- So if g > 1, then k ≢ -2 (mod r)!
          -- So r does NOT divide 2 + k!
          -- So if g > 1, and ¬ r ∣ x_seq (r^2 - 3), then r does NOT divide x_seq (r^2 - 2)!
          -- But we know r MUST divide x_seq (r^2 - 2)!
          -- So we must have g = 1!
          -- Yes!
          -- But this still requires us to know r ∣ x_seq (r^2 - 2) to get the contradiction!
          -- But we are trying to prove r ∣ x_seq (r^2 - 2)!
          -- So we cannot assume it!
          -- Is there any other way?
          -- Wait!
          -- What if we prove `r ∣ x_seq (r^2 - 1)` for `r = 1021` by `decide`?
          -- Yes!
          -- Let's check how long it takes to prove `1021 ∣ x_seq (1021^2 - 1)` using `decide`!
          -- Wait!
          -- `1021^2 - 1 = 1042440`.
          -- Computing `x_seq 1042440` in Lean 4 kernel using `decide` might take too long (since it has 1042440 steps).
          -- But wait!
          -- In `/workspace/leanproject/Submission/Spec.lean`, they proved `1019 ∣ x_seq (1019^2 - 1)` by:
          -- Finding `n = 17321` such that `1019 ∣ x_seq 17321`!
          -- And `17321` is much smaller than `1019^2 - 1 = 1038360`!
          -- So they only had to run `decide` for `17321` steps!
          -- Which took less than a second!
          -- Yes!
          -- Can we do the same for `1021`?
          -- For `r = 1021`, let's find the first `n` where `1021 ∣ x_seq n`!
          -- Let's run a python script to find this `n`!

      have : r^2 ≥ 25 := by nlinarith
      omega
    have h_prod_eq : k * m = r^2 - 2 := hm.symm
    rw [h_prod_val, h_prod_eq] at h_prod_ge
    have : r^2 ≥ 25 := by nlinarith
    omega
