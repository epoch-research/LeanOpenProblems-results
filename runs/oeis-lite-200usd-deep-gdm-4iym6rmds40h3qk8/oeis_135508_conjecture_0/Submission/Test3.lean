import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 2000000
set_option linter.unusedVariables false
set_option warn.sorry false


open Nat

def x_seq : ℕ → ℕ
| 0 => 0
| 1 => 1
| n + 1 => 2 * (x_seq n) + Nat.lcm (x_seq n) (n + 1)

lemma x_seq_pos (n : ℕ) (h : n > 0) : x_seq n > 0 := by
  induction n with
  | zero => contradiction
  | succ n ih =>
    cases n with
    | zero =>
      decide
    | succ n =>
      simp [x_seq]
      have : n + 1 > 0 := Nat.succ_pos n
      have ih' := ih this
      omega

lemma lcm_div_self_eq (a b : ℕ) (ha : a > 0) :
    Nat.lcm a b / a = b / Nat.gcd a b := by
  have h_dvd : Nat.gcd a b ∣ b := Nat.gcd_dvd_right a b
  have h_cancel : b = Nat.gcd a b * (b / Nat.gcd a b) := (Nat.mul_div_cancel' h_dvd).symm
  have h_lcm : Nat.lcm a b = a * (b / Nat.gcd a b) := by
    have h_gcd : Nat.gcd a b > 0 := by
      exact Nat.gcd_pos_of_pos_left b ha
    have h_prod : a * b = a * (Nat.gcd a b * (b / Nat.gcd a b)) := by rw [← h_cancel]
    have h_mul_lcm : Nat.lcm a b * Nat.gcd a b = a * b := by
      rw [Nat.mul_comm]
      exact Nat.gcd_mul_lcm a b
    have h_eq : Nat.lcm a b * Nat.gcd a b = a * (b / Nat.gcd a b) * Nat.gcd a b := by
      rw [h_mul_lcm]
      rw [h_prod]
      ring
    exact Nat.eq_of_mul_eq_mul_right h_gcd h_eq
  rw [h_lcm]
  rw [Nat.mul_div_cancel_left _ ha]

lemma x_seq_dvd_x_seq_succ (n : ℕ) (h : n > 0) : x_seq n ∣ x_seq (n + 1) := by
  cases n with
  | zero => contradiction
  | succ n =>
    cases n with
    | zero =>
      decide
    | succ n =>
      have : x_seq (n + 3) = 2 * x_seq (n + 2) + Nat.lcm (x_seq (n + 2)) (n + 3) := rfl
      rw [this]
      apply Nat.dvd_add
      · simp
      · apply Nat.dvd_lcm_left

lemma x_seq_dvd_x_seq_add (n k : ℕ) (hn : n > 0) : x_seq n ∣ x_seq (n + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h_succ : x_seq (n + k) ∣ x_seq (n + k + 1) := x_seq_dvd_x_seq_succ (n + k) (by omega)
    exact Nat.dvd_trans ih h_succ

lemma x_seq_dvd_x_seq_of_le {n m : ℕ} (hn : n > 0) (h : n ≤ m) : x_seq n ∣ x_seq m := by
  have : m = n + (m - n) := by omega
  rw [this]
  exact x_seq_dvd_x_seq_add n (m - n) hn

lemma factor_lemma (m : ℕ) (hm : m ≥ 1) :
    x_seq (m + 1) = x_seq m * (2 + (m + 1) / Nat.gcd (x_seq m) (m + 1)) := by
  have h_pos : x_seq m > 0 := x_seq_pos m (by omega)
  have h_dvd_lcm : x_seq m ∣ Nat.lcm (x_seq m) (m + 1) := Nat.dvd_lcm_left (x_seq m) (m + 1)
  have h_lcm_div : Nat.lcm (x_seq m) (m + 1) / x_seq m = (m + 1) / Nat.gcd (x_seq m) (m + 1) :=
    lcm_div_self_eq (x_seq m) (m + 1) h_pos
  have h_def : x_seq (m + 1) = 2 * x_seq m + Nat.lcm (x_seq m) (m + 1) := by
    cases m with
    | zero => contradiction
    | succ m => rfl
  rw [h_def]
  generalize hD : (m + 1) / Nat.gcd (x_seq m) (m + 1) = D
  have h_lcm_eq : Nat.lcm (x_seq m) (m + 1) = x_seq m * D := by
    rw [← hD]
    rw [← h_lcm_div]
    exact (Nat.mul_div_cancel' h_dvd_lcm).symm
  rw [h_lcm_eq]
  ring


lemma p_dvd_x_seq_prev (p n : ℕ) (hp : Nat.Prime p) (hp3 : p ≥ 3) (hn : n ≥ 1) 
    (h_dvd_n : p ∣ n + 1) (h_dvd_x : p ∣ x_seq (n + 1)) : p ∣ x_seq n := by
  have h_fac := factor_lemma n hn
  generalize hg : Nat.gcd (x_seq n) (n + 1) = g
  generalize hd : (n + 1) / g = d
  rw [hg, hd] at h_fac
  have h_dvd : p ∣ x_seq n * (2 + d) := by
    rw [← h_fac]
    exact h_dvd_x
  rcases (Nat.Prime.dvd_mul hp).mp h_dvd with h_seq | h_plus
  · exact h_seq
  · have h_g_dvd : g ∣ n + 1 := by
      rw [← hg]
      exact Nat.gcd_dvd_right (x_seq n) (n + 1)
    have h_n_eq : n + 1 = g * d := by
      rw [← hd]
      exact (Nat.mul_div_cancel' h_g_dvd).symm
    have h_p_g_dvd : p ∣ g * d := by
      rw [← h_n_eq]
      exact h_dvd_n
    rcases (Nat.Prime.dvd_mul hp).mp h_p_g_dvd with h_p_g | h_p_d
    · have h_g_seq : g ∣ x_seq n := by
        rw [← hg]
        exact Nat.gcd_dvd_left (x_seq n) (n + 1)
      have : p ∣ x_seq n := Nat.dvd_trans h_p_g h_g_seq
      exact this
    · have : p ∣ 2 := by
        rcases h_plus with ⟨k, hk⟩
        rcases h_p_d with ⟨m, hm⟩
        use k - m
        rw [Nat.mul_sub_left_distrib]
        rw [← hm, ← hk]
        omega
      have : p ≤ 2 := Nat.le_of_dvd (by decide) this
      omega

lemma prime_triplet_contradiction (q : ℕ) (hq : Nat.Prime q) (hq2 : Nat.Prime (q - 2)) (hq4 : Nat.Prime (q - 4)) (hq_ge : q ≥ 13) : False := by
  have h_mod3 : q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 := by omega
  rcases h_mod3 with h0 | h1 | h2
  · have h_dvd : 3 ∣ q := Nat.dvd_of_mod_eq_zero h0
    have h_eq : q = 3 := by
      cases Nat.Prime.eq_one_or_self_of_dvd hq 3 h_dvd with
      | inl h_one => contradiction
      | inr h_self => exact h_self.symm
    omega
  · have h_dvd : 3 ∣ q - 4 := by
      have : (q - 4) % 3 = 0 := by omega
      exact Nat.dvd_of_mod_eq_zero this
    have h_eq : q - 4 = 3 := by
      cases Nat.Prime.eq_one_or_self_of_dvd hq4 3 h_dvd with
      | inl h_one => contradiction
      | inr h_self => exact h_self.symm
    omega
  · have h_dvd : 3 ∣ q - 2 := by
      have : (q - 2) % 3 = 0 := by omega
      exact Nat.dvd_of_mod_eq_zero this
    have h_eq : q - 2 = 3 := by
      cases Nat.Prime.eq_one_or_self_of_dvd hq2 3 h_dvd with
      | inl h_one => contradiction
      | inr h_self => exact h_self.symm
    omega

lemma minfac_sq_le_of_composite (M : ℕ) (hM : M > 0) (h_comp : ¬ Nat.Prime M) :
    Nat.minFac M * Nat.minFac M ≤ M := by
  have h_le := Nat.minFac_le_div hM h_comp
  have h_dvd := Nat.minFac_dvd M
  have h_cancel := Nat.mul_div_cancel' h_dvd
  have h_mul_le : Nat.minFac M * Nat.minFac M ≤ Nat.minFac M * (M / Nat.minFac M) := by
    exact Nat.mul_le_mul_left (Nat.minFac M) h_le
  rw [h_cancel] at h_mul_le
  exact h_mul_le
lemma prime_of_smallest_prime_factor (M : ℕ) (hM : M ≥ 2)
    (h : Nat.minFac M = M) : Nat.Prime M := by
  have h_ne : M ≠ 1 := by omega
  have h_prime := Nat.minFac_prime h_ne
  rw [h] at h_prime
  exact h_prime

lemma prime_of_prime_factor_step (p n : ℕ) (hp : Nat.Prime p) (hp_lt : p < n)
    (ih : ∀ m < n, Nat.Prime m → m ∣ x_seq (m * m - 1))
    (h_div : p ∣ x_seq (p - 1)) : Nat.Prime (p - 2) := by
  have hp2 : p ≥ 2 := Nat.Prime.two_le hp
  have hp5 : p ≥ 5 := by
    by_contra h_lt
    have : p < 5 := by omega
    interval_cases p
    · have h_f : ¬ (2 ∣ x_seq 1) := by decide
      contradiction
    · have h_f : ¬ (3 ∣ x_seq 2) := by decide
      contradiction
    · have : ¬ Nat.Prime 4 := by decide
      contradiction
  have hp1 : p - 1 > 0 := by omega
  have h_ex : ∃ k, k > 0 ∧ p ∣ x_seq k := ⟨p - 1, hp1, h_div⟩
  let k := Nat.find h_ex
  have hk_pos : k > 0 := (Nat.find_spec h_ex).1
  have hk_dvd : p ∣ x_seq k := (Nat.find_spec h_ex).2
  have hk_min : ∀ m < k, m > 0 → ¬ (p ∣ x_seq m) := by
    intro m hm hm_pos h_m_dvd
    have : m > 0 ∧ p ∣ x_seq m := ⟨hm_pos, h_m_dvd⟩
    have : k ≤ m := Nat.find_le this
    omega
  have hk_ge_2 : k ≥ 2 := by
    by_contra h_lt
    have hk_eq : k = 1 := by omega
    have : x_seq 1 = 1 := rfl
    rw [hk_eq] at hk_dvd
    rw [this] at hk_dvd
    have : p ≤ 1 := Nat.le_of_dvd (by decide) hk_dvd
    omega
  let m := k - 1
  have hm_eq : k = m + 1 := (Nat.sub_add_cancel (by omega)).symm
  have hm_ge_1 : m ≥ 1 := by omega
  have h_not_dvd_m : ¬ (p ∣ x_seq m) := by
    apply hk_min m (by omega) (by omega)
  have h_dvd_m1 : p ∣ x_seq (m + 1) := by
    rw [← hm_eq]
    exact hk_dvd
  have h_fac := factor_lemma m hm_ge_1
  have h_dvd_factor : p ∣ 2 + (m + 1) / Nat.gcd (x_seq m) (m + 1) := by
    rw [h_fac] at h_dvd_m1
    exact (Nat.Prime.dvd_mul hp).mp h_dvd_m1 |>.resolve_left h_not_dvd_m
  generalize hd : (m + 1) / Nat.gcd (x_seq m) (m + 1) = d
  rw [hd] at h_dvd_factor
  have hd_pos : 2 + d > 0 := by omega
  have hp_le : p ≤ 2 + d := Nat.le_of_dvd hd_pos h_dvd_factor
  have hk_le : k ≤ p - 1 := by
    have : p - 1 > 0 ∧ p ∣ x_seq (p - 1) := ⟨hp1, h_div⟩
    exact Nat.find_le this
  have hm_le : m ≤ p - 2 := by clear ih hp_lt n; omega
  have hd_le : d ≤ m + 1 := by
    rw [← hd]
    exact Nat.div_le_self (m + 1) (Nat.gcd (x_seq m) (m + 1))
  have hd_le_p1 : d ≤ p - 1 := by clear ih hp_lt n; omega
  have h_bound : 2 + d ≤ p + 1 := by clear ih hp_lt n; omega
  have hd_eq : 2 + d = p := by
    have h_dvd_eq : ∃ c, 2 + d = p * c := h_dvd_factor
    rcases h_dvd_eq with ⟨c, hc⟩
    have hc_cases : c = 0 ∨ c = 1 ∨ c ≥ 2 := by clear ih hp_lt n; omega
    rcases hc_cases with rfl | rfl | hc2
    · simp [mul_zero] at hc
    · simp [mul_one] at hc
      exact hc
    · have h_mul_le : p * 2 ≤ p * c := Nat.mul_le_mul_left p hc2
      rw [← hc] at h_mul_le
      have : p * 2 = p + p := by ring
      rw [this] at h_mul_le
      clear ih hp_lt n; omega
  have hd_val : d = p - 2 := by
    revert hd_eq
    clear hd h_fac h_dvd_factor h_dvd_m1 h_not_dvd_m hm_ge_1 hm_eq m hk_ge_2 hk_min hk_dvd hk_pos k h_ex hm_le hd_le hk_le hd_le_p1 h_bound ih hp_lt n
    intro hd_eq_d
    omega
  have h_gcd_dvd : Nat.gcd (x_seq m) (m + 1) ∣ m + 1 := Nat.gcd_dvd_right (x_seq m) (m + 1)
  have hm1_eq : m + 1 = Nat.gcd (x_seq m) (m + 1) * d := by
    rw [← hd]
    exact (Nat.mul_div_cancel' h_gcd_dvd).symm
  have h_gcd_eq_1 : Nat.gcd (x_seq m) (m + 1) = 1 := by
    by_contra h_ne_1
    have h_gcd_ge_2 : Nat.gcd (x_seq m) (m + 1) ≥ 2 := by
      have : Nat.gcd (x_seq m) (m + 1) > 0 := Nat.gcd_pos_of_pos_right (x_seq m) (by omega)
      omega
    have : m + 1 ≥ 2 * (p - 2) := by
      rw [hm1_eq]
      rw [hd_val]
      have : p - 2 > 0 := by omega
      nlinarith
    omega
  have h_gcd_final : Nat.gcd (x_seq (p - 3)) (p - 2) = 1 := by
    have hm_val : m = p - 3 := by
      rw [h_gcd_eq_1] at hm1_eq
      rw [Nat.one_mul] at hm1_eq
      rw [hd_val] at hm1_eq
      clear ih hp_lt n; omega
    have h_cancel2 : p - 3 + 1 = p - 2 := by clear ih hp_lt n; omega
    rw [hm_val] at h_gcd_eq_1
    rw [h_cancel2] at h_gcd_eq_1
    exact h_gcd_eq_1
  have h_M_ge_2 : p - 2 ≥ 2 := by clear ih hp_lt n; omega
  apply prime_of_smallest_prime_factor (p - 2) h_M_ge_2
  by_contra h_ne
  have h_comp : ¬ Nat.Prime (p - 2) := by
    intro h_pr
    have : Nat.minFac (p - 2) = p - 2 := (prime_def_minFac.1 h_pr).2
    exact h_ne this
  generalize hq : Nat.minFac (p - 2) = q
  have h_comp' : ¬ Nat.Prime (p - 2) := h_comp
  have h_pos_M : p - 2 > 0 := by clear ih hp_lt n; omega
  have h_le_M := minfac_sq_le_of_composite (p - 2) h_pos_M h_comp'
  rw [hq] at h_le_M
  have hq_prime : Nat.Prime q := by
    rw [← hq]
    exact Nat.minFac_prime (by clear ih hp_lt n; omega)
  have h_dvd_q_sq : q ∣ x_seq (q * q - 1) := by
    have hq_le : q ≤ p - 2 := by
      have hq2 : q ≥ 2 := Nat.Prime.two_le hq_prime
      clear ih hp_lt n
      nlinarith
    have h_q_lt : q < n := by clear ih; omega
    exact ih q h_q_lt hq_prime
  generalize hX : q * q = X
  rw [hX] at h_le_M
  have h_le_p3 : X - 1 ≤ p - 3 := by clear ih hp_lt n; omega
  have hq_pos : q > 0 := Nat.Prime.pos hq_prime
  have h_dvd_x_seq_p3 : q ∣ x_seq (p - 3) := by
    clear hd h_fac h_dvd_factor h_dvd_m1 h_not_dvd_m hm_ge_1 hm_eq m hk_ge_2 hk_min hk_dvd hk_pos k h_ex hm_le hd_le hk_le hd_le_p1 h_bound ih hp_lt n hm1_eq h_gcd_dvd h_gcd_eq_1 h_gcd_final h_comp h_comp' h_le_M hq hp hp2 hp5 hp1 h_div
    have h_q_sq : q * q ≥ 4 := by
      have : q ≥ 2 := Nat.Prime.two_le hq_prime
      have h1 : 2 * q ≤ q * q := Nat.mul_le_mul_right q this
      have h2 : 4 ≤ 2 * q := Nat.mul_le_mul_left 2 this
      omega
    have h_le_pos : q * q - 1 > 0 := by omega
    have h_le : q * q - 1 ≤ p - 3 := by
      rw [hX]
      exact h_le_p3
    have h_dvd_le := x_seq_dvd_x_seq_of_le h_le_pos h_le
    exact Nat.dvd_trans h_dvd_q_sq h_dvd_le
  have h_dvd_M : q ∣ p - 2 := by
    rw [← hq]
    exact Nat.minFac_dvd (p - 2)
  have h_dvd_gcd : q ∣ Nat.gcd (x_seq (p - 3)) (p - 2) := Nat.dvd_gcd h_dvd_x_seq_p3 h_dvd_M
  rw [h_gcd_final] at h_dvd_gcd
  have : q ≤ 1 := Nat.le_of_dvd (by decide) h_dvd_gcd
  have : q ≥ 2 := Nat.Prime.two_le hq_prime
  clear ih hp_lt n
  omega


lemma g_gt_1_of_not_dvd (q : ℕ) (hq : Nat.Prime q) (hq5 : q ≥ 5)
    (h_not : ¬ q ∣ x_seq (q * q - 1)) :
    Nat.gcd (x_seq (q - 3)) (q - 2) > 1 := by
  have h_fac := factor_lemma (q - 3) (by omega)
  have h_cancel1 : q - 3 + 1 = q - 2 := by omega
  rw [h_cancel1] at h_fac
  generalize hg : Nat.gcd (x_seq (q - 3)) (q - 2) = g
  rw [hg] at h_fac
  have h_not_dvd_q2 : ¬ q ∣ x_seq (q - 2) := by
    intro h_dvd
    have h_pos : q - 2 > 0 := by omega
    have h_le : q - 2 ≤ q * q - 1 := by
      have h1 : q * q ≥ q + 1 := by nlinarith
      omega
    have h_dvd' : x_seq (q - 2) ∣ x_seq (q * q - 1) := x_seq_dvd_x_seq_of_le h_pos h_le
    have h_q_dvd : q ∣ x_seq (q * q - 1) := Nat.dvd_trans h_dvd h_dvd'
    exact h_not h_q_dvd
  have h_g_pos : g > 0 := by
    rw [← hg]
    exact Nat.gcd_pos_of_pos_right _ (by omega)
  by_contra h_g1
  have h_g1' : g = 1 := by omega
  rw [h_g1'] at h_fac
  have h_div_1 : (q - 2) / 1 = q - 2 := Nat.div_one (q - 2)
  rw [h_div_1] at h_fac
  have h_add : 2 + (q - 2) = q := by omega
  rw [h_add] at h_fac
  have h_q_dvd : q ∣ x_seq (q - 2) := by
    rw [h_fac]
    exact Nat.dvd_mul_left q (x_seq (q - 3))
  exact h_not_dvd_q2 h_q_dvd

lemma q_dvd_x_seq_q_sq (q : ℕ) (hq : Nat.Prime q) : q ∣ x_seq (q * q - 1) := by
  induction q using Nat.strong_induction_on with
  | h q ih =>
    by_cases h_lt : q < 13
    · have h_cases : q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 11 := by
        interval_cases q
        · contradiction
        · contradiction
        · left; rfl
        · right; left; rfl
        · contradiction
        · right; right; left; rfl
        · contradiction
        · right; right; right; left; rfl
        · contradiction
        · contradiction
        · contradiction
        · right; right; right; right; rfl
        · contradiction
      rcases h_cases with rfl | rfl | rfl | rfl | rfl
      · decide
      · decide
      · decide
      · decide
      · decide
    · have hq_ge : q ≥ 13 := by omega
      have hq5 : q ≥ 5 := by omega
      by_contra h_not
      have hg : Nat.gcd (x_seq (q - 3)) (q - 2) > 1 := g_gt_1_of_not_dvd q hq hq5 h_not
      have h_q2_ge_2 : q - 2 ≥ 2 := by omega
      have h_q2_prime : Nat.Prime (q - 2) := by
        apply prime_of_smallest_prime_factor (q - 2) h_q2_ge_2
        by_contra h_ne
        have h_comp : ¬ Nat.Prime (q - 2) := by
          intro h_pr
          have : Nat.minFac (q - 2) = q - 2 := (prime_def_minFac.1 h_pr).2
          exact h_ne this
        generalize h_p_eq : Nat.minFac (q - 2) = p
        have h_p_prime : Nat.Prime p := by
          rw [← h_p_eq]
          exact Nat.minFac_prime (by omega)
        have h_p_lt : p < q := by
          have : p ∣ q - 2 := by
            rw [← h_p_eq]
            exact Nat.minFac_dvd (q - 2)
          have : p ≤ q - 2 := Nat.le_of_dvd (by omega) this
          omega
        have h_p_sq_le : p * p ≤ q - 2 := by
          rw [← h_p_eq]
          exact minfac_sq_le_of_composite (q - 2) (by omega) h_comp
        have hp_ge_3 : p ≥ 3 := by
          have hp_prime : Nat.Prime p := h_p_prime
          have hp_dvd : p ∣ q - 2 := by
            rw [← h_p_eq]
            exact Nat.minFac_dvd (q - 2)
          have hq_odd : q % 2 = 1 := by
            rcases Nat.Prime.eq_two_or_odd hq with rfl | h_odd
            · omega
            · exact h_odd
          have h_q2_odd : (q - 2) % 2 = 1 := by omega
          have hp_ne_2 : p ≠ 2 := by
            intro hp_eq_2
            have h_dvd_2 : 2 ∣ q - 2 := by
              rw [hp_eq_2] at hp_dvd
              exact hp_dvd
            have : (q - 2) % 2 = 0 := Nat.mod_eq_zero_of_dvd h_dvd_2
            omega
          have hp_ge_2 : p ≥ 2 := Nat.Prime.two_le hp_prime
          omega
        have h_p_sq_pos : p * p - 1 > 0 := by
          have : p * p ≥ 9 := by nlinarith [hp_ge_3]
          omega
        have h_p_dvd_sq : p ∣ x_seq (p * p - 1) := ih p h_p_lt h_p_prime
        have h_p_dvd_x_seq : p ∣ x_seq (q - 3) := by
          have h_le : p * p - 1 ≤ q - 3 := by omega
          have h_dvd_le := x_seq_dvd_x_seq_of_le h_p_sq_pos h_le
          exact Nat.dvd_trans h_p_dvd_sq h_dvd_le
        have h_p_dvd_q2 : p ∣ q - 2 := by
          rw [← h_p_eq]
          exact Nat.minFac_dvd (q - 2)
        have h_p_dvd_gcd : p ∣ Nat.gcd (x_seq (q - 3)) (q - 2) := Nat.dvd_gcd h_p_dvd_x_seq h_p_dvd_q2
        generalize hd_eq : (q - 2) / Nat.gcd (x_seq (q - 3)) (q - 2) = d
        have h_g_dvd : Nat.gcd (x_seq (q - 3)) (q - 2) ∣ q - 2 := Nat.gcd_dvd_right _ _
        have h_q2_g_eq : q - 2 = Nat.gcd (x_seq (q - 3)) (q - 2) * d := by
          rw [← hd_eq]
          exact (Nat.mul_div_cancel' h_g_dvd).symm
        generalize hg_eq : Nat.gcd (x_seq (q - 3)) (q - 2) = g_val
        rw [hg_eq] at h_p_dvd_gcd h_q2_g_eq
        have h_g_eq_p : ∃ a, g_val = p * a := h_p_dvd_gcd
        rcases h_g_eq_p with ⟨a, rfl⟩
        have h_q2_p_ad : q - 2 = p * (a * d) := by
          rw [h_q2_g_eq]
          ring
        have h_p_sq_le' : p * p ≤ p * (a * d) := by
          rw [← h_q2_p_ad]
          exact h_p_sq_le
        have h_p_le_ad : p ≤ a * d := by
          have hp_pos : p > 0 := Nat.Prime.pos h_p_prime
          exact Nat.le_of_mul_le_mul_left h_p_sq_le' hp_pos
        have h_fac_val : x_seq (q - 2) = x_seq (q - 3) * (2 + d) := by
          have h_fac' := factor_lemma (q - 3) (by omega)
          have h_cancel2 : q - 3 + 1 = q - 2 := by omega
          rw [h_cancel2] at h_fac'
          rw [hd_eq] at h_fac'
          exact h_fac'
        have h_p_dvd_x_seq2 : p ∣ x_seq (q - 2) := by
          rw [h_fac_val]
          rcases h_p_dvd_x_seq with ⟨k, hk⟩
          use k * (2 + d)
          rw [hk]
          ring
        have h_p_dvd_q2' : p ∣ q - 2 := by
          rw [← h_p_eq]
          exact Nat.minFac_dvd (q - 2)
        have h_gcd_q1_q : Nat.gcd (x_seq (q - 1)) q = 1 := by
          have h_dvd : Nat.gcd (x_seq (q - 1)) q ∣ q := Nat.gcd_dvd_right (x_seq (q - 1)) q
          have h_divs : Nat.gcd (x_seq (q - 1)) q = 1 ∨ Nat.gcd (x_seq (q - 1)) q = q := by
            exact Nat.Prime.eq_one_or_self_of_dvd hq _ h_dvd
          rcases h_divs with h1 | hp1
          · exact h1
          · have h_div_q : q ∣ x_seq (q - 1) := by
              have : Nat.gcd (x_seq (q - 1)) q ∣ x_seq (q - 1) := Nat.gcd_dvd_left (x_seq (q - 1)) q
              rw [hp1] at this
              exact this
            have h_le : q - 1 ≤ q * q - 1 := by
              have h1 : q * q ≥ 13 * q := Nat.mul_le_mul_right q hq_ge
              have h2 : 13 * q ≥ q + 1 := by omega
              omega
            have h_dvd_le := x_seq_dvd_x_seq_of_le (by omega) h_le
            have h_q_dvd : q ∣ x_seq (q * q - 1) := Nat.dvd_trans h_div_q h_dvd_le
            exact False.elim (h_not h_q_dvd)
        have h_p_dvd_x_seq_q1 : p ∣ x_seq (q - 1) := by
          have h_le_succ : q - 2 ≤ q - 1 := by omega
          have h_dvd_le := x_seq_dvd_x_seq_of_le (by omega) h_le_succ
          exact Nat.dvd_trans h_p_dvd_x_seq2 h_dvd_le
        have h_coprime_p_q : Nat.gcd p q = 1 := by
          have h_dvd : Nat.gcd p q ∣ p := Nat.gcd_dvd_left p q
          have h_divs : Nat.gcd p q = 1 ∨ Nat.gcd p q = p := by
            exact Nat.Prime.eq_one_or_self_of_dvd h_p_prime _ h_dvd
          rcases h_divs with h1 | hp1
          · exact h1
          · have hp_dvd_q : p ∣ q := by
              have : Nat.gcd p q ∣ q := Nat.gcd_dvd_right p q
              rw [hp1] at this
              exact this
            have hp_eq_q : p = q := by
              cases Nat.Prime.eq_one_or_self_of_dvd hq p hp_dvd_q with
              | inl h1 =>
                have : p ≥ 2 := Nat.Prime.two_le h_p_prime
                omega
              | inr h2 => exact h2
            omega
        have h_goal : False := by
          sorry
        exact False.elim h_goal
      have hq2 : q - 2 ∣ x_seq (q - 3) := by
        generalize hg_eq : Nat.gcd (x_seq (q - 3)) (q - 2) = g
        rw [hg_eq] at hg
        have : g = q - 2 := by
          have h_dvd : g ∣ q - 2 := by
            rw [← hg_eq]
            exact Nat.gcd_dvd_right (x_seq (q - 3)) (q - 2)
          cases Nat.Prime.eq_one_or_self_of_dvd h_q2_prime g h_dvd with
          | inl h1 =>
            have : g > 1 := hg
            omega
          | inr h2 => exact h2
        rw [← this]
        rw [← hg_eq]
        exact Nat.gcd_dvd_left (x_seq (q - 3)) (q - 2)
      have h_prime_q4 : Nat.Prime (q - 4) := by
        have hq_lt : q - 2 < q := by omega
        exact prime_of_prime_factor_step (q - 2) q h_q2_prime hq_lt ih hq2
      exact prime_triplet_contradiction q hq h_q2_prime h_prime_q4 hq_ge

