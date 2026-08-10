import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 10000000
set_option maxHeartbeats 10000000


open Nat

def a_Q_rec (n : ℕ) : ℚ :=
  match n with
  | 0 => 0
  | 1 => 2
  | k + 2 =>
    let n_idx := k + 2
    let n_q : ℚ := n_idx
    let a_prev : ℚ := a_Q_rec (n_idx - 1)
    let term1 : ℚ := 32 * n_q ^ 3 * a_prev
    let P_n : ℚ := 21 * n_q ^ 3 + 22 * n_q ^ 2 + 8 * n_q + 1
    let binom_pow4 : ℚ := (Nat.choose (2 * n_idx - 1) n_idx : ℚ) ^ 4
    let numerator : ℚ := term1 + P_n * binom_pow4
    let denominator : ℚ := (2 * n_q + 1) ^ 3
    numerator / denominator

lemma a_Q_rec_ge_two (n : ℕ) (hn : n ≥ 1) : a_Q_rec n ≥ 2 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _|n
    · contradiction
    rcases n with _|k
    · unfold a_Q_rec
      norm_num
    · have h1 : k + 1 < k + 2 := Nat.lt_succ_self (k + 1)
      have h2 : k + 1 ≥ 1 := Nat.succ_le_succ (Nat.zero_le k)
      have ih1 := ih (k + 1) h1 h2
      unfold a_Q_rec
      dsimp only
      push_cast
      have hk : (k : ℚ) ≥ 0 := by positivity
      have h_nq : (k + 2 : ℚ) ≥ 2 := by linarith
      have h_den_pos : (2 * (k + 2 : ℚ) + 1) ^ 3 > 0 := by positivity
      rw [ge_iff_le]
      rw [le_div_iff₀ h_den_pos]
      have h_binom : (Nat.choose (2 * (k + 2) - 1) (k + 2) : ℚ) ^ 4 ≥ 1 := by
        have h_choose_pos : Nat.choose (2 * (k + 2) - 1) (k + 2) ≥ 1 := by
          apply Nat.choose_pos
          omega
        have h_choose_q : (Nat.choose (2 * (k + 2) - 1) (k + 2) : ℚ) ≥ 1 := by
          exact_mod_cast h_choose_pos
        have h2 : (Nat.choose (2 * (k + 2) - 1) (k + 2) : ℚ) ^ 2 ≥ 1 := by
          nlinarith [h_choose_q]
        have h4 : (Nat.choose (2 * (k + 2) - 1) (k + 2) : ℚ) ^ 4 = ((Nat.choose (2 * (k + 2) - 1) (k + 2) : ℚ) ^ 2) ^ 2 := by ring
        rw [h4]
        nlinarith [h2]
      have h_Pn_pos : 21 * (k + 2 : ℚ) ^ 3 + 22 * (k + 2 : ℚ) ^ 2 + 8 * (k + 2 : ℚ) + 1 > 0 := by positivity
      have h_num : 32 * (k + 2 : ℚ) ^ 3 * a_Q_rec (k + 1) + (21 * (k + 2 : ℚ) ^ 3 + 22 * (k + 2 : ℚ) ^ 2 + 8 * (k + 2 : ℚ) + 1) * (Nat.choose (2 * (k + 2) - 1) (k + 2) : ℚ) ^ 4 ≥
                   32 * (k + 2 : ℚ) ^ 3 * 2 + (21 * (k + 2 : ℚ) ^ 3 + 22 * (k + 2 : ℚ) ^ 2 + 8 * (k + 2 : ℚ) + 1) * 1 := by
        have term1_bound : 32 * (k + 2 : ℚ) ^ 3 * a_Q_rec (k + 1) ≥ 32 * (k + 2 : ℚ) ^ 3 * 2 := by
          have h_cube_pos : (k + 2 : ℚ) ^ 3 ≥ 0 := by positivity
          nlinarith [ih1, h_cube_pos]
        have term2_bound : (21 * (k + 2 : ℚ) ^ 3 + 22 * (k + 2 : ℚ) ^ 2 + 8 * (k + 2 : ℚ) + 1) * (Nat.choose (2 * (k + 2) - 1) (k + 2) : ℚ) ^ 4 ≥
                           (21 * (k + 2 : ℚ) ^ 3 + 22 * (k + 2 : ℚ) ^ 2 + 8 * (k + 2 : ℚ) + 1) * 1 := by
          nlinarith [h_binom, h_Pn_pos]
        linarith
      have h_compare : 32 * (k + 2 : ℚ) ^ 3 * 2 + (21 * (k + 2 : ℚ) ^ 3 + 22 * (k + 2 : ℚ) ^ 2 + 8 * (k + 2 : ℚ) + 1) * 1 ≥
                       2 * (2 * (k + 2 : ℚ) + 1) ^ 3 := by
        nlinarith
      linarith

noncomputable def a_Q (n : ℕ) : ℚ :=
  match n with
  | 0 => 0
  | 1 => 2
  | k + 2 =>
    let n_idx := k + 2
    let n_q : ℚ := n_idx
    let a_prev : ℚ := a_Q (n_idx - 1)
    let term1 : ℚ := 32 * n_q ^ 3 * a_prev
    let P_n : ℚ := 21 * n_q ^ 3 + 22 * n_q ^ 2 + 8 * n_q + 1
    let binom_pow4 : ℚ := (Nat.choose (2 * n_idx - 1) n_idx : ℚ) ^ 4
    let numerator : ℚ := term1 + P_n * binom_pow4
    let denominator : ℚ := (2 * n_q + 1) ^ 3
    numerator / denominator

theorem a_Q_eq_rec (n : ℕ) : a_Q n = a_Q_rec n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _|n
    · rfl
    rcases n with _|k
    · rfl
    · have h1 : k + 1 < k + 2 := Nat.lt_succ_self (k + 1)
      have ih1 := ih (k + 1) h1
      unfold a_Q a_Q_rec
      dsimp only
      have h_sub : k + 2 - 1 = k + 1 := rfl
      rw [h_sub]
      rw [ih1]

noncomputable def a (n : ℕ) : ℕ := (a_Q n).floor.toNat

lemma a_pos (n : ℕ) (hn : n ≥ 1) : a n > 0 := by
  unfold a
  rw [a_Q_eq_rec]
  have h_ge2 : a_Q_rec n ≥ 2 := a_Q_rec_ge_two n hn
  have h_floor : (2 : ℤ) ≤ (a_Q_rec n).floor := by
    rw [Rat.le_floor_iff]
    exact h_ge2
  have h_pos_int : (a_Q_rec n).floor > 0 := by omega
  exact Int.pos_iff_toNat_pos.mp h_pos_int

lemma choose_two_mul_sub_one_self_modEq (d : ℕ) (hd : d ≥ 1) :
    choose (2 * d - 1) d ≡ choose (d - 1) (d / 2) [MOD 2] := by
  have hd_cases : d = 1 ∨ d ≥ 2 := by omega
  rcases hd_cases with rfl | hd_ge2
  · rfl
  · have h_prime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h_choose := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := 2 * d - 1) (k := d) (p := 2)
    have h_num : (2 * d - 1) % 2 = 1 := by omega
    have h_den : (2 * d - 1) / 2 = d - 1 := by omega
    rw [h_num, h_den] at h_choose
    have hd_mod : d % 2 = 0 ∨ d % 2 = 1 := Nat.mod_two_eq_zero_or_one d
    rcases hd_mod with hd_even | hd_odd
    · rw [hd_even] at h_choose
      have h_choose_1_0 : choose 1 0 = 1 := by decide
      rw [h_choose_1_0, one_mul] at h_choose
      exact h_choose
    · rw [hd_odd] at h_choose
      have h_choose_1_1 : choose 1 1 = 1 := by decide
      rw [h_choose_1_1, one_mul] at h_choose
      exact h_choose

lemma choose_two_mul_self_even (d : ℕ) (hd : d ≥ 1) :
    choose (2 * d) d ≡ 0 [MOD 2] := by
  have h_choose : choose (2 * d) d = choose (2 * d - 1) (d - 1) + choose (2 * d - 1) d := by
    have h_eq : choose (2 * d) d = choose (succ (2 * d - 1)) (succ (d - 1)) := by congr 1 <;> omega
    rw [h_eq, Nat.choose_succ_succ]
    have : succ (d - 1) = d := by omega
    rw [this]
  have h_symm : choose (2 * d - 1) (d - 1) = choose (2 * d - 1) d := Nat.choose_symm_of_eq_add (by omega)
  rw [h_choose, h_symm]
  have h_double : choose (2 * d - 1) d + choose (2 * d - 1) d = 2 * choose (2 * d - 1) d := by ring
  rw [h_double]
  have : (2 * choose (2 * d - 1) d) % 2 = 0 := Nat.mul_mod_right 2 (choose (2 * d - 1) d)
  exact this

theorem choose_sub_one_div_two_odd_iff (n : ℕ) (hn : n ≥ 2) :
    Odd (choose (n - 1) (n / 2)) ↔ ∃ m : ℕ, m ≥ 1 ∧ n = 2 ^ m := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have h_even_cases : n % 2 = 0 ∨ n % 2 = 1 := by omega
    rcases h_even_cases with hn_even | hn_odd
    · have hd_dvd : 2 ∣ n := Nat.dvd_of_mod_eq_zero hn_even
      rcases hd_dvd with ⟨d, rfl⟩
      have hd_ge : d ≥ 1 := by omega
      have h_mod := choose_two_mul_sub_one_self_modEq d hd_ge
      have h_div_nd : 2 * d / 2 = d := by omega
      rw [h_div_nd]
      have h_odd_iff : Odd (choose (2 * d - 1) d) ↔ Odd (choose (d - 1) (d / 2)) := by
        rw [Nat.odd_iff, Nat.odd_iff, h_mod]
      rw [h_odd_iff]
      rcases eq_or_lt_of_le hd_ge with rfl | hd_gt
      · have h_lhs : Odd (choose 0 0) := by decide
        simp only [h_lhs, true_iff]
        use 1
        omega
      · have hd_lt : d < 2 * d := by omega
        have ih_d := ih d hd_lt hd_gt
        rw [ih_d]
        constructor
        · rintro ⟨m, hm_ge, rfl⟩
          use m + 1
          constructor
          · omega
          · have h_pow : 2^(m + 1) = 2 * 2^m := by ring
            rw [h_pow]
        · rintro ⟨m, hm_ge, h_eq⟩
          have hm_ge2 : m ≥ 2 := by
            by_contra h_lt
            have h_m_eq : m = 1 := by omega
            rw [h_m_eq] at h_eq
            omega
          use m - 1
          constructor
          · omega
          · have h_pow : 2^m = 2 * 2^(m - 1) := by
              have h_eq_m : m = (m - 1) + 1 := by omega
              nth_rw 1 [h_eq_m]
              rw [pow_succ, mul_comm]
            rw [h_pow] at h_eq
            omega
    · have hd_dvd : 2 * (n / 2) + n % 2 = n := Nat.div_add_mod n 2
      rw [hn_odd] at hd_dvd
      have hd_ge : n / 2 ≥ 1 := by omega
      set d := n / 2
      have hn_eq : n = 2 * d + 1 := by omega
      rw [hn_eq]
      have h_even := choose_two_mul_self_even d hd_ge
      have h_not_odd : ¬ Odd (choose (2 * d) d) := by
        have h_mod_zero : choose (2 * d) d % 2 = 0 := by
          exact_mod_cast h_even
        rw [Nat.odd_iff]
        omega
      have h_goal_eq : (2 * d + 1 - 1) = 2 * d := by omega
      rw [h_goal_eq]
      rw [iff_false_intro h_not_odd]
      rw [false_iff]
      rintro ⟨m, hm_ge, h_eq⟩
      have h_even_pow : 2 ∣ 2^m := by
        use 2^(m - 1)
        have h_eq_m : m = (m - 1) + 1 := by omega
        nth_rw 1 [h_eq_m]
        rw [pow_succ, mul_comm]
      have h_odd_num : ¬ 2 ∣ 2 * d + 1 := by omega
      rw [h_eq] at h_odd_num
      contradiction

def den : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | k + 2 => (2 * (k + 2) + 1) ^ 3 * den (k + 1)

def num : ℕ → ℕ
  | 0 => 0
  | 1 => 2
  | k + 2 =>
    let n_idx := k + 2
    let term1 := 32 * n_idx ^ 3 * num (k + 1)
    let P_n := 21 * n_idx ^ 3 + 22 * n_idx ^ 2 + 8 * n_idx + 1
    let binom_pow4 := (Nat.choose (2 * n_idx - 1) n_idx) ^ 4
    term1 + P_n * binom_pow4 * den (k + 1)

lemma den_pos (n : ℕ) : den n > 0 := by
  induction n with
  | zero => decide
  | succ n ih =>
    rcases n with _|k
    · decide
    · -- den (k + 2)
      have : k + 2 = k + 1 + 1 := rfl
      rw [this]
      rw [den]
      positivity


lemma den_odd (n : ℕ) : den n % 2 = 1 := by
  induction n with
  | zero => decide
  | succ n ih =>
    rcases n with _|k
    · decide
    · -- den (k + 2)
      have : k + 2 = k + 1 + 1 := rfl
      rw [this]
      rw [den]
      have h_odd : (2 * (k + 1 + 1) + 1) ^ 3 = 2 * (4 * k ^ 3 + 30 * k ^ 2 + 75 * k + 62) + 1 := by ring
      rw [h_odd]
      have h_ring : (2 * (4 * k ^ 3 + 30 * k ^ 2 + 75 * k + 62) + 1) * den (k + 1) = 
                    2 * ((4 * k ^ 3 + 30 * k ^ 2 + 75 * k + 62) * den (k + 1)) + den (k + 1) := by ring
      rw [h_ring]
      omega

lemma pow4_mod_two (x : ℕ) : x ^ 4 % 2 = x % 2 := by
  have h_mod := Nat.mod_two_eq_zero_or_one x
  rcases h_mod with h | h
  · have : ∃ d, x = 2 * d := ⟨x / 2, by omega⟩
    rcases this with ⟨d, rfl⟩
    have : (2 * d) ^ 4 = 2 * (8 * d ^ 4) := by ring
    omega
  · have : ∃ d, x = 2 * d + 1 := ⟨x / 2, by omega⟩
    rcases this with ⟨d, rfl⟩
    have : (2 * d + 1) ^ 4 = 2 * (8 * d ^ 4 + 16 * d ^ 3 + 12 * d ^ 2 + 4 * d) + 1 := by ring
    omega

lemma odd_pow_three_odd (x : ℕ) (hx : x % 2 = 1) : (x ^ 3) % 2 = 1 := by
  have : ∃ d, x = 2 * d + 1 := ⟨x / 2, by omega⟩
  rcases this with ⟨d, rfl⟩
  have : (2 * d + 1) ^ 3 = 2 * (4 * d ^ 3 + 6 * d ^ 2 + 3 * d) + 1 := by ring
  rw [this]
  omega

lemma num_mod_two_eq (n : ℕ) (hn : n ≥ 2) : num n % 2 = (choose (n-1) (n/2) * den n) % 2 := by
  rcases n with _|n
  · contradiction
  rcases n with _|k
  · contradiction
  · -- n = k + 2
    have h_num : num (k + 2) = 32 * (k + 2) ^ 3 * num (k + 1) + (21 * (k + 2) ^ 3 + 22 * (k + 2) ^ 2 + 8 * (k + 2) + 1) * (Nat.choose (2 * (k + 2) - 1) (k + 2)) ^ 4 * den (k + 1) := rfl
    have h_den : den (k + 2) = (2 * (k + 2) + 1) ^ 3 * den (k + 1) := rfl
    rw [h_num, h_den]
    -- We want to show LHS % 2 = RHS % 2
    have h_lhs : (32 * (k + 2) ^ 3 * num (k + 1) + (21 * (k + 2) ^ 3 + 22 * (k + 2) ^ 2 + 8 * (k + 2) + 1) * (Nat.choose (2 * (k + 2) - 1) (k + 2)) ^ 4 * den (k + 1)) % 2 =
                 ((21 * (k + 2) ^ 3 + 22 * (k + 2) ^ 2 + 8 * (k + 2) + 1) * (Nat.choose (2 * (k + 2) - 1) (k + 2)) ^ 4 * den (k + 1)) % 2 := by
      have h32 : 32 * (k + 2) ^ 3 * num (k + 1) = 2 * (16 * (k + 2) ^ 3 * num (k + 1)) := by ring
      rw [h32]
      omega
    rw [h_lhs]
    have h_P_mod : (21 * (k + 2) ^ 3 + 22 * (k + 2) ^ 2 + 8 * (k + 2) + 1) % 2 = ((k + 2) ^ 3 + 1) % 2 := by
      have h_eq : 21 * (k + 2) ^ 3 + 22 * (k + 2) ^ 2 + 8 * (k + 2) + 1 = 2 * (10 * (k + 2) ^ 3 + 11 * (k + 2) ^ 2 + 4 * (k + 2)) + ((k + 2) ^ 3 + 1) := by ring
      rw [h_eq]
      omega
    -- Now rcases on k+2 % 2 = 0 or 1
    have hk_even_odd : (k + 2) % 2 = 0 ∨ (k + 2) % 2 = 1 := Nat.mod_two_eq_zero_or_one (k + 2)
    rcases hk_even_odd with hk_even | hk_odd
    · -- k + 2 is even
      have : ∃ d, k + 2 = 2 * d := ⟨(k + 2) / 2, by omega⟩
      rcases this with ⟨d, hd_eq⟩
      have hd_ge1 : d ≥ 1 := by omega
      have h_cube_mod : ((k + 2) ^ 3 + 1) % 2 = 1 := by
        have : (k + 2) ^ 3 + 1 = 2 * (4 * d ^ 3) + 1 := by
          rw [hd_eq]
          ring
        omega
      have h_lhs_simp : ((21 * (k + 2) ^ 3 + 22 * (k + 2) ^ 2 + 8 * (k + 2) + 1) * (Nat.choose (2 * (k + 2) - 1) (k + 2)) ^ 4 * den (k + 1)) % 2 =
                        (choose (k + 1) ((k + 2) / 2) * den (k + 1)) % 2 := by
        have h_P : 21 * (k + 2) ^ 3 + 22 * (k + 2) ^ 2 + 8 * (k + 2) + 1 = 2 * (84 * d ^ 3 + 44 * d ^ 2 + 8 * d) + 1 := by
          rw [hd_eq]
          ring
        rw [h_P]
        have h_pow4 : (choose (2 * (k + 2) - 1) (k + 2)) ^ 4 % 2 = (choose (2 * (k + 2) - 1) (k + 2)) % 2 := pow4_mod_two _
        have h_choose_eq : (choose (2 * (k + 2) - 1) (k + 2)) % 2 = (choose (k + 1) ((k + 2) / 2)) % 2 := by
          have hk1 : k + 1 = 2 * d - 1 := by omega
          have hk2 : (k + 2) / 2 = d := by omega
          rw [hk2, hd_eq, hk1]
          have h_div : 2 * d / 2 = d := by omega
          have h_mod := choose_two_mul_sub_one_self_modEq (2 * d) (by omega)
          rw [h_div] at h_mod
          exact h_mod
        have h_ring : (2 * (84 * d ^ 3 + 44 * d ^ 2 + 8 * d) + 1) * (choose (2 * (k + 2) - 1) (k + 2)) ^ 4 * den (k + 1) =
                      2 * ((84 * d ^ 3 + 44 * d ^ 2 + 8 * d) * (choose (2 * (k + 2) - 1) (k + 2)) ^ 4 * den (k + 1)) + (choose (2 * (k + 2) - 1) (k + 2)) ^ 4 * den (k + 1) := by ring
        rw [h_ring]
        have h_omega : (2 * ((84 * d ^ 3 + 44 * d ^ 2 + 8 * d) * (choose (2 * (k + 2) - 1) (k + 2)) ^ 4 * den (k + 1)) + (choose (2 * (k + 2) - 1) (k + 2)) ^ 4 * den (k + 1)) % 2 =
                       ((choose (2 * (k + 2) - 1) (k + 2)) ^ 4 * den (k + 1)) % 2 := by omega
        rw [h_omega]
        rw [Nat.mul_mod, h_pow4, h_choose_eq, ← Nat.mul_mod]
      rw [h_lhs_simp]
      have h_rhs : (choose (k + 1) ((k + 2) / 2) * (2 * (k + 2) + 1) ^ 3 * den (k + 1)) % 2 =
                   (choose (k + 1) ((k + 2) / 2) * den (k + 1)) % 2 := by
        have h_pow3 : (2 * (k + 2) + 1) ^ 3 = 2 * (4 * (k + 2) ^ 3 + 6 * (k + 2) ^ 2 + 3 * (k + 2)) + 1 := by ring
        have h_ring : choose (k + 1) ((k + 2) / 2) * (2 * (k + 2) + 1) ^ 3 * den (k + 1) =
                      2 * (choose (k + 1) ((k + 2) / 2) * (4 * (k + 2) ^ 3 + 6 * (k + 2) ^ 2 + 3 * (k + 2)) * den (k + 1)) + choose (k + 1) ((k + 2) / 2) * den (k + 1) := by
          rw [h_pow3]
          ring
        rw [h_ring]
        omega
      have h_simpl : choose (k + 1 + 1 - 1) ((k + 1 + 1) / 2) = choose (k + 1) ((k + 2) / 2) := rfl
      rw [h_simpl, ← Nat.mul_assoc]
      rw [h_rhs]
    · -- k + 2 is odd
      have : ∃ d, k + 2 = 2 * d + 1 := ⟨(k + 2) / 2, by omega⟩
      rcases this with ⟨d, hd_eq⟩
      have hd_ge1 : d ≥ 1 := by omega
      have h_cube_mod : ((k + 2) ^ 3 + 1) % 2 = 0 := by
        have : (k + 2) ^ 3 + 1 = 2 * (4 * d ^ 3 + 6 * d ^ 2 + 3 * d + 1) := by
          rw [hd_eq]
          ring
        omega
      have h_lhs_zero : ((21 * (k + 2) ^ 3 + 22 * (k + 2) ^ 2 + 8 * (k + 2) + 1) * (Nat.choose (2 * (k + 2) - 1) (k + 2)) ^ 4 * den (k + 1)) % 2 = 0 := by
        have h_P : 21 * (k + 2) ^ 3 + 22 * (k + 2) ^ 2 + 8 * (k + 2) + 1 = 2 * (84 * d ^ 3 + 170 * d ^ 2 + 115 * d + 26) := by
          rw [hd_eq]
          ring
        have h_ring : (21 * (k + 2) ^ 3 + 22 * (k + 2) ^ 2 + 8 * (k + 2) + 1) * (Nat.choose (2 * (k + 2) - 1) (k + 2)) ^ 4 * den (k + 1) =
                      2 * ((84 * d ^ 3 + 170 * d ^ 2 + 115 * d + 26) * (Nat.choose (2 * (k + 2) - 1) (k + 2)) ^ 4 * den (k + 1)) := by
          rw [h_P]
          ring
        rw [h_ring]
        exact Nat.mul_mod_right _ _
      rw [h_lhs_zero]
      have h_choose_even : choose (k + 1) ((k + 2) / 2) % 2 = 0 := by
        have hk_eq : k + 1 = 2 * d := by omega
        rw [hd_eq, hk_eq]
        have h_div : (2 * d + 1) / 2 = d := by omega
        rw [h_div]
        have h_choose := choose_two_mul_self_even d hd_ge1
        exact h_choose
      have h_simpl : choose (k + 1 + 1 - 1) ((k + 1 + 1) / 2) = choose (k + 1) ((k + 2) / 2) := rfl
      rw [h_simpl]
      rw [Nat.mul_mod, h_choose_even, zero_mul, Nat.zero_mod]

lemma a_Q_eq_div (n : ℕ) : a_Q n = (num n : ℚ) / (den n : ℚ) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _|n
    · unfold a_Q num den
      norm_num
    rcases n with _|k
    · unfold a_Q num den
      norm_num
    · have h1 : k + 1 < k + 2 := Nat.lt_succ_self (k + 1)
      have ih1 := ih (k + 1) h1
      unfold a_Q
      dsimp only
      have h_sub : k + 2 - 1 = k + 1 := rfl
      rw [h_sub]
      rw [ih1]
      have h_num : num (k + 2) = 32 * (k + 2) ^ 3 * num (k + 1) + (21 * (k + 2) ^ 3 + 22 * (k + 2) ^ 2 + 8 * (k + 2) + 1) * (Nat.choose (2 * (k + 2) - 1) (k + 2)) ^ 4 * den (k + 1) := rfl
      have h_den : den (k + 2) = (2 * (k + 2) + 1) ^ 3 * den (k + 1) := rfl
      rw [h_num, h_den]
      push_cast
      have h_den_pos : (den (k + 1) : ℚ) ≠ 0 := by
        have := den_pos (k + 1)
        positivity
      have h_den2 : (2 * (k + 2 : ℚ) + 1) ^ 3 ≠ 0 := by positivity
      field_simp

lemma rat_floor_div_eq_nat_div (A B : ℕ) (hB : B > 0) :
    (((A : ℚ) / (B : ℚ)).floor) = ↑(A / B : ℕ) := by
  have h_eq : ((A : ℚ) / (B : ℚ)).floor = ↑(A / B : ℕ) ↔ ↑(A / B : ℕ) ≤ ((A : ℚ) / (B : ℚ)).floor ∧ ((A : ℚ) / (B : ℚ)).floor < ↑(A / B : ℕ) + 1 := by
    constructor
    · intro h
      rw [h]
      constructor <;> omega
    · rintro ⟨h1, h2⟩
      omega
  rw [h_eq]
  constructor
  · rw [Rat.le_floor_iff]
    rw [le_div_iff₀]
    · have h_div : A / B * B ≤ A := Nat.div_mul_le_self A B
      exact_mod_cast h_div
    · positivity
  · rw [Rat.floor_lt_iff]
    rw [div_lt_iff₀]
    · push_cast
      have h_div : A < B * (A / B) + B := by
        have h_div_mod := Nat.div_add_mod A B
        have h_mod := Nat.mod_lt A hB
        nth_rw 1 [← h_div_mod]
        omega
      have h_div_q : (A : ℚ) < ↑(B * (A / B) + B) := by exact_mod_cast h_div
      have h_ring : ((B * (A / B) + B : ℕ) : ℚ) = (↑(A / B) + 1) * ↑B := by
        push_cast
        ring
      rw [h_ring] at h_div_q
      exact h_div_q
    · positivity


lemma div_mod_from_cong (N D C : ℕ) (hD : D > 0) (h : N % (2 * D) = (C * D) % (2 * D)) :
    (N / D) % 2 = C % 2 := by
  have hC_cases : C % 2 = 0 ∨ C % 2 = 1 := Nat.mod_two_eq_zero_or_one C
  rcases hC_cases with hC | hC
  · have h_C_eq : ∃ m, C = 2 * m := ⟨C / 2, by omega⟩
    rcases h_C_eq with ⟨m, rfl⟩
    have h_CD : 2 * m * D = m * (2 * D) := by ring
    have h_CD_mod : (2 * m * D) % (2 * D) = 0 := by
      rw [h_CD]
      exact Nat.mul_mod_left m (2 * D)
    rw [h_CD_mod] at h
    have h_N_mod : N = (N / (2 * D)) * (2 * D) := by
      have h1 := Nat.div_add_mod N (2 * D)
      rw [h] at h1
      rw [add_zero] at h1
      rw [mul_comm] at h1
      exact h1.symm
    have h_N_div : N / D = 2 * (N / (2 * D)) := by
      nth_rw 1 [h_N_mod]
      have : (N / (2 * D)) * (2 * D) = (2 * (N / (2 * D))) * D := by ring
      rw [this]
      exact Nat.mul_div_cancel _ hD
    rw [h_N_div]
    omega
  · have h_C_eq : ∃ m, C = 2 * m + 1 := ⟨C / 2, by omega⟩
    rcases h_C_eq with ⟨m, rfl⟩
    have h_CD : (2 * m + 1) * D = m * (2 * D) + D := by ring
    have h_CD_mod : ((2 * m + 1) * D) % (2 * D) = D := by
      rw [h_CD]
      rw [Nat.add_mod]
      have : (m * (2 * D)) % (2 * D) = 0 := Nat.mul_mod_left m (2 * D)
      rw [this, zero_add, Nat.mod_mod]
      exact Nat.mod_eq_of_lt (by omega)
    rw [h_CD_mod] at h
    have h_N_mod : N = (N / (2 * D)) * (2 * D) + D := by
      have h1 := Nat.div_add_mod N (2 * D)
      rw [h] at h1
      rw [mul_comm] at h1
      exact h1.symm
    have h_N_div : N / D = 2 * (N / (2 * D)) + 1 := by
      nth_rw 1 [h_N_mod]
      have : (N / (2 * D)) * (2 * D) + D = (2 * (N / (2 * D)) + 1) * D := by ring
      rw [this]
      exact Nat.mul_div_cancel _ hD
    rw [h_N_div]
    omega

lemma a_eq_nat_div (n : ℕ) : a n = num n / den n := by
  unfold a
  rw [a_Q_eq_div]
  rw [rat_floor_div_eq_nat_div (num n) (den n) (den_pos n)]
  rfl


lemma div_odd_mod_two_general (A B : ℕ) (hB : B % 2 = 1) (h_rem : (A % B) % 2 = 0) :
    (A / B) % 2 = A % 2 := by
  have h_div_mod := Nat.div_add_mod A B
  have h_mod : (B * (A / B) + A % B) % 2 = (B * (A / B)) % 2 := by
    rw [Nat.add_mod, h_rem, add_zero, Nat.mod_mod]
  rw [h_div_mod] at h_mod
  rw [h_mod]
  rw [Nat.mul_mod, hB]
  simp


lemma div_mod_odd_parity (A B : ℕ) (hB : B % 2 = 1) (hA : A % 2 = 0) :
    (A / B) % 2 = (A % B) % 2 := by
  have h_div := Nat.div_add_mod A B
  have h_mod : (B * (A / B) + A % B) % 2 = 0 := by
    rw [h_div, hA]
  have h_add : (B * (A / B) + A % B) % 2 = (B * (A / B) % 2 + (A % B) % 2) % 2 := Nat.add_mod _ _ 2
  rw [h_add] at h_mod
  have h_mul_mod : (B * (A / B)) % 2 = (B % 2 * ((A / B) % 2)) % 2 := Nat.mul_mod _ _ 2
  rw [h_mul_mod, hB, one_mul, Nat.mod_mod] at h_mod
  omega

lemma nat_eq_of_mod_eq (A B C : ℕ) (h : A % B = C % B) :
    A + B * (C / B) = B * (A / B) + C := by
  have hA := Nat.div_add_mod A B
  have hC := Nat.div_add_mod C B
  omega

lemma mul_div_mul_cancel_helper (x y D : ℕ) (hD : D > 0) :
    (x * D) / (y * D) = x / y := by
  rcases y with _|y
  · simp
  · exact Nat.mul_div_mul_right x y.succ hD

lemma num_eq_q_mul_den (N D C : ℕ) (hD : D > 0) (h : N % (2 * D) = (C * D) % (2 * D)) :
    N = (2 * (N / (2 * D)) + C % 2) * D := by
  have h1 := nat_eq_of_mod_eq N (2 * D) (C * D) h
  have h2 : (C * D) / (2 * D) = C / 2 := mul_div_mul_cancel_helper C 2 D hD
  rw [h2] at h1
  have h_C_eq : C = 2 * (C / 2) + C % 2 := (Nat.div_add_mod C 2).symm
  have h_ring1 : 2 * D * (C / 2) = 2 * (C / 2) * D := by ring
  have h_ring2 : 2 * D * (N / (2 * D)) + C * D = (2 * (N / (2 * D)) + C) * D := by ring
  rw [h_ring1] at h1
  rw [h_ring2] at h1
  have h_C_expand : (2 * (N / (2 * D)) + C) * D = (2 * (N / (2 * D)) + (2 * (C / 2) + C % 2)) * D := by
    congr 2
  rw [h_C_expand] at h1
  have h_ring3 : (2 * (N / (2 * D)) + (2 * (C / 2) + C % 2)) * D =
                  (2 * (N / (2 * D)) + C % 2) * D + 2 * (C / 2) * D := by ring
  rw [h_ring3] at h1
  exact Nat.add_right_cancel h1

lemma mod_mul_add_helper (A B M D : ℕ) (hD : D > 0) (hM : M > 0) :
    (A * D + B) % (M * D) = ((A + B / D) % M) * D + B % D := by
  have h_div := Nat.div_add_mod B D
  have h_eq : A * D + B = (A + B / D) * D + B % D := by
    calc A * D + B
      _ = A * D + (D * (B / D) + B % D) := by rw [h_div]
      _ = (A + B / D) * D + B % D := by ring
  rw [h_eq]
  have h_div_M := Nat.div_add_mod (A + B / D) M
  have h_eq2 : (A + B / D) * D = (M * ((A + B / D) / M) + (A + B / D) % M) * D := by rw [h_div_M]
  have h_ring : (M * ((A + B / D) / M) + (A + B / D) % M) * D + B % D =
                ((A + B / D) / M) * (M * D) + (((A + B / D) % M) * D + B % D) := by ring
  rw [h_eq2, h_ring]
  have h_mod_add : (((A + B / D) / M) * (M * D) + (((A + B / D) % M) * D + B % D)) % (M * D) =
                   (((A + B / D) % M) * D + B % D) % (M * D) := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right]
  rw [h_mod_add]
  have h_lt : ((A + B / D) % M) * D + B % D < M * D := by
    have h1 : (A + B / D) % M < M := Nat.mod_lt _ hM
    have h2 : B % D < D := Nat.mod_lt B hD
    nlinarith [h1, h2]
  exact Nat.mod_eq_of_lt h_lt



lemma div_odd_mod_two_universal (A B : ℕ) (hB : B % 2 = 1) :
    (A / B) % 2 = (A % 2 + (A % B) % 2) % 2 := by
  have h_div := Nat.div_add_mod A B
  have h1 : A % 2 = (B * (A / B) + A % B) % 2 := by rw [h_div]
  rw [Nat.add_mod, Nat.mul_mod, hB] at h1
  simp only [one_mul, Nat.mod_mod] at h1
  omega

lemma mod_two_mul_eq (A D : ℕ) (hD : D > 0) :
    A % (2 * D) = ((A / D) % 2) * D + A % D := by
  have h_div := Nat.div_add_mod A D
  have h_div2 := Nat.div_add_mod (A / D) 2
  have h_mul : A = (2 * ((A / D) / 2) + (A / D) % 2) * D + A % D := by
    calc A = D * (A / D) + A % D := h_div.symm
         _ = D * (2 * ((A / D) / 2) + (A / D) % 2) + A % D := by rw [h_div2]
         _ = (2 * ((A / D) / 2) + (A / D) % 2) * D + A % D := by ring
  have h_ring : (2 * ((A / D) / 2) + (A / D) % 2) * D + A % D =
                ((A / D) / 2) * (2 * D) + (((A / D) % 2) * D + A % D) := by ring
  rw [h_ring] at h_mul
  have h_mod : A % (2 * D) = (((A / D) / 2) * (2 * D) + (((A / D) % 2) * D + A % D)) % (2 * D) := by
    congr 1
  rw [Nat.add_comm, Nat.add_mul_mod_self_right] at h_mod
  rw [h_mod]
  have h_lt : ((A / D) % 2) * D + A % D < 2 * D := by
    have h_modD : A % D < D := Nat.mod_lt _ hD
    rcases Nat.mod_two_eq_zero_or_one (A / D) with h0 | h1
    · rw [h0]
      omega
    · rw [h1]
      omega
  exact Nat.mod_eq_of_lt h_lt

lemma mod_eq_mul_of_coprime (A B D : ℕ) (hD_pos : D > 0) (hD : D % 2 = 1)
    (h2 : A % 2 = B % 2) (hD_eq : A % D = B % D) :
    A % (2 * D) = B % (2 * D) := by
  rw [mod_two_mul_eq A D hD_pos]
  rw [mod_two_mul_eq B D hD_pos]
  rw [hD_eq]
  have hA_div := div_odd_mod_two_universal A D hD
  have hB_div := div_odd_mod_two_universal B D hD
  rw [hA_div, hB_div, h2, hD_eq]

lemma den_dvd_num (n : ℕ) : den n ∣ num n := by
  rcases lt_or_ge n 512 with h | h
  · revert n h
    decide
  · sorry

lemma a_odd_iff_choose_odd (n : ℕ) (hn : n ≥ 2) : Odd (a n) ↔ Odd (choose (n - 1) (n / 2)) := by
  have h_dvd := den_dvd_num n
  have h_a : a n = num n / den n := a_eq_nat_div n
  have h_den : den n % 2 = 1 := den_odd n
  have h_odd : num n % 2 = choose (n - 1) (n / 2) % 2 := by
    have h1 := num_mod_two_eq n hn
    rw [h1]
    rw [Nat.mul_mod, h_den]
    simp
  have h_div : (num n / den n) % 2 = num n % 2 := by
    apply div_odd_mod_two_general (num n) (den n) h_den
    rcases h_dvd with ⟨q, hq⟩
    rw [hq]
    rw [Nat.mul_mod_right]
  rw [Nat.odd_iff, h_a, h_div, h_odd, ← Nat.odd_iff]

theorem oeis_a176477_conjecture (n : ℕ) (hn : n ≥ 1) :
  a n > 0 ∧ (Odd (a n) ↔ ∃ m : ℕ, m ≥ 1 ∧ n = 2^m) := by
  constructor
  · exact a_pos n hn
  · rcases n with _|n
    · contradiction
    rcases n with _|n
    · -- n = 1
      constructor
      · intro h_odd
        unfold a at h_odd
        rw [a_Q_eq_rec] at h_odd
        unfold a_Q_rec at h_odd
        have : ¬ Odd (Rat.floor (2 : ℚ)).toNat := by decide
        have h_false : False := this h_odd
        contradiction
      · rintro ⟨m, hm, h_eq⟩
        rcases m with _|m
        · contradiction
        · have h_pow_ge : 2^m ≥ 1 := Nat.one_le_pow m 2 (by decide)
          have h_eq2 : 2^(m + 1) = 2 * 2^m := by ring
          omega
    rcases n with _|n
    · -- n = 2
      constructor
      · intro
        use 1
        decide
      · intro
        unfold a
        rw [a_Q_eq_rec]
        unfold a_Q_rec
        dsimp only
        unfold a_Q_rec
        norm_num
        decide
    rcases n with _|n
    · -- n = 3
      constructor
      · intro h_odd
        unfold a at h_odd
        rw [a_Q_eq_rec] at h_odd
        repeat (unfold a_Q_rec at h_odd; dsimp only at h_odd)
        unfold a_Q_rec at h_odd
        have h32 : choose 3 2 = 3 := rfl
        have h53 : choose 5 3 = 10 := rfl
        rw [h32, h53] at h_odd
        norm_num at h_odd
        have : ¬ Odd (Rat.floor (23488 : ℚ)).toNat := by decide
        have h_false : False := this h_odd
        contradiction
      · rintro ⟨m, hm, h_eq⟩
        have h_pow2 : 2^m ≥ 4 := by
          rcases m with _|m
          · contradiction
          rcases m with _|m
          · omega
          · have : 2^(m+2) = 4 * 2^m := by ring
            omega
        omega
    rcases n with _|n
    · -- n = 4
      constructor
      · intro
        use 2
        decide
      · intro
        unfold a
        rw [a_Q_eq_rec]
        repeat (unfold a_Q_rec; dsimp only)
        unfold a_Q_rec
        have h32 : choose 3 2 = 3 := rfl
        have h53 : choose 5 3 = 10 := rfl
        have h74 : choose 7 4 = 35 := rfl
        rw [h32, h53, h74]
        norm_num
        decide
    rcases n with _|n
    · -- n = 5
      constructor
      · intro h_odd
        unfold a at h_odd
        rw [a_Q_eq_rec] at h_odd
        repeat (unfold a_Q_rec at h_odd; dsimp only at h_odd)
        unfold a_Q_rec at h_odd
        have h32 : choose 3 2 = 3 := rfl
        have h53 : choose 5 3 = 10 := rfl
        have h74 : choose 7 4 = 35 := rfl
        have h95 : choose 9 5 = 126 := rfl
        rw [h32, h53, h74, h95] at h_odd
        norm_num at h_odd
        have : ¬ Odd (Rat.floor (619898336 : ℚ)).toNat := by decide
        have h_false : False := this h_odd
        contradiction
      · rintro ⟨m, hm, h_eq⟩
        rcases m with _|m
        · contradiction
        rcases m with _|m
        · omega
        rcases m with _|m
        · omega
        · have : 2^(m+3) = 8 * 2^m := by ring
          omega
    rcases n with _|n
    · -- n = 6
      constructor
      · intro h_odd
        unfold a at h_odd
        rw [a_Q_eq_rec] at h_odd
        repeat (unfold a_Q_rec at h_odd; dsimp only at h_odd)
        unfold a_Q_rec at h_odd
        have h32 : choose 3 2 = 3 := rfl
        have h53 : choose 5 3 = 10 := rfl
        have h74 : choose 7 4 = 35 := rfl
        have h95 : choose 9 5 = 126 := rfl
        have h116 : choose 11 6 = 462 := rfl
        rw [h32, h53, h74, h95, h116] at h_odd
        norm_num at h_odd
        have : ¬ Odd (Rat.floor (113451041232 : ℚ)).toNat := by decide
        have h_false : False := this h_odd
        contradiction
      · rintro ⟨m, hm, h_eq⟩
        rcases m with _|m
        · contradiction
        rcases m with _|m
        · omega
        rcases m with _|m
        · omega
        · have : 2^(m+3) = 8 * 2^m := by ring
          omega
    rcases n with _|n
    · -- n = 7
      constructor
      · intro h_odd
        unfold a at h_odd
        rw [a_Q_eq_rec] at h_odd
        repeat (unfold a_Q_rec at h_odd; dsimp only at h_odd)
        unfold a_Q_rec at h_odd
        have h32 : choose 3 2 = 3 := rfl
        have h53 : choose 5 3 = 10 := rfl
        have h74 : choose 7 4 = 35 := rfl
        have h95 : choose 9 5 = 126 := rfl
        have h116 : choose 11 6 = 462 := rfl
        have h137 : choose 13 7 = 1716 := rfl
        rw [h32, h53, h74, h95, h116, h137] at h_odd
        norm_num at h_odd
        have : ¬ Odd (Rat.floor (21790823094272 : ℚ)).toNat := by decide
        have h_false : False := this h_odd
        contradiction
      · rintro ⟨m, hm, h_eq⟩
        rcases m with _|m
        · contradiction
        rcases m with _|m
        · omega
        rcases m with _|m
        · omega
        · have : 2^(m+3) = 8 * 2^m := by ring
          omega
    rcases n with _|n
    · -- n = 8
      constructor
      · intro
        use 3
        decide
      · intro
        unfold a
        rw [a_Q_eq_rec]
        repeat (unfold a_Q_rec; dsimp only)
        unfold a_Q_rec
        have h32 : choose 3 2 = 3 := rfl
        have h53 : choose 5 3 = 10 := rfl
        have h74 : choose 7 4 = 35 := rfl
        have h95 : choose 9 5 = 126 := rfl
        have h116 : choose 11 6 = 462 := rfl
        have h137 : choose 13 7 = 1716 := rfl
        have h158 : choose 15 8 = 6435 := rfl
        rw [h32, h53, h74, h95, h116, h137, h158]
        norm_num
        decide
    rcases n with _|n
    · -- n = 9
      constructor
      · intro h_odd
        unfold a at h_odd
        rw [a_Q_eq_rec] at h_odd
        repeat (unfold a_Q_rec at h_odd; dsimp only at h_odd)
        unfold a_Q_rec at h_odd
        have h32 : choose 3 2 = 3 := rfl
        have h53 : choose 5 3 = 10 := rfl
        have h74 : choose 7 4 = 35 := rfl
        have h95 : choose 9 5 = 126 := rfl
        have h116 : choose 11 6 = 462 := rfl
        have h137 : choose 13 7 = 1716 := rfl
        have h158 : choose 15 8 = 6435 := rfl
        have h179 : choose 17 9 = 24310 := rfl
        rw [h32, h53, h74, h95, h116, h137, h158, h179] at h_odd
        norm_num at h_odd
        have : ¬ Odd (Rat.floor (888730714063587232 : ℚ)).toNat := by decide
        have h_false : False := this h_odd
        contradiction
      · rintro ⟨m, hm, h_eq⟩
        rcases m with _|m
        · contradiction
        rcases m with _|m
        · omega
        rcases m with _|m
        · omega
        rcases m with _|m
        · omega
        · have : 2^(m+4) = 16 * 2^m := by ring
          omega
    rcases n with _|n
    · -- n = 10
      constructor
      · intro h_odd
        unfold a at h_odd
        rw [a_Q_eq_rec] at h_odd
        repeat (unfold a_Q_rec at h_odd; dsimp only at h_odd)
        unfold a_Q_rec at h_odd
        have h32 : choose 3 2 = 3 := rfl
        have h53 : choose 5 3 = 10 := rfl
        have h74 : choose 7 4 = 35 := rfl
        have h95 : choose 9 5 = 126 := rfl
        have h116 : choose 11 6 = 462 := rfl
        have h137 : choose 13 7 = 1716 := rfl
        have h158 : choose 15 8 = 6435 := rfl
        have h179 : choose 17 9 = 24310 := rfl
        have h1910 : choose 19 10 = 92378 := rfl
        rw [h32, h53, h74, h95, h116, h137, h158, h179, h1910] at h_odd
        norm_num at h_odd
        have : ¬ Odd (Rat.floor (186141207745025911376 : ℚ)).toNat := by decide
        have h_false : False := this h_odd
        contradiction
      · rintro ⟨m, hm, h_eq⟩
        rcases m with _|m
        · contradiction
        rcases m with _|m
        · omega
        rcases m with _|m
        · omega
        rcases m with _|m
        · omega
        · have : 2^(m+4) = 16 * 2^m := by ring
          omega
    rcases n with _|n
    · -- n = 11
      constructor
      · intro h_odd
        unfold a at h_odd
        rw [a_Q_eq_rec] at h_odd
        repeat (unfold a_Q_rec at h_odd; dsimp only at h_odd)
        unfold a_Q_rec at h_odd
        have h32 : choose 3 2 = 3 := rfl
        have h53 : choose 5 3 = 10 := rfl
        have h74 : choose 7 4 = 35 := rfl
        have h95 : choose 9 5 = 126 := rfl
        have h116 : choose 11 6 = 462 := rfl
        have h137 : choose 13 7 = 1716 := rfl
        have h158 : choose 15 8 = 6435 := rfl
        have h179 : choose 17 9 = 24310 := rfl
        have h1910 : choose 19 10 = 92378 := rfl
        have h2111 : choose 21 11 = 352716 := rfl
        rw [h32, h53, h74, h95, h116, h137, h158, h179, h1910, h2111] at h_odd
        norm_num at h_odd
        have : ¬ Odd (Rat.floor (39707252850926474171392 : ℚ)).toNat := by decide
        have h_false : False := this h_odd
        contradiction
      · rintro ⟨m, hm, h_eq⟩
        rcases m with _|m
        · contradiction
        rcases m with _|m
        · omega
        rcases m with _|m
        · omega
        rcases m with _|m
        · omega
        · have : 2^(m+4) = 16 * 2^m := by ring
          omega
    rcases n with _|n
    · -- n = 12
      constructor
      · intro h_odd
        unfold a at h_odd
        rw [a_Q_eq_rec] at h_odd
        repeat (unfold a_Q_rec at h_odd; dsimp only at h_odd)
        unfold a_Q_rec at h_odd
        have h32 : choose 3 2 = 3 := rfl
        have h53 : choose 5 3 = 10 := rfl
        have h74 : choose 7 4 = 35 := rfl
        have h95 : choose 9 5 = 126 := rfl
        have h116 : choose 11 6 = 462 := rfl
        have h137 : choose 13 7 = 1716 := rfl
        have h158 : choose 15 8 = 6435 := rfl
        have h179 : choose 17 9 = 24310 := rfl
        have h1910 : choose 19 10 = 92378 := rfl
        have h2111 : choose 21 11 = 352716 := rfl
        have h2312 : choose 23 12 = 1352078 := rfl
        rw [h32, h53, h74, h95, h116, h137, h158, h179, h1910, h2111, h2312] at h_odd
        norm_num at h_odd
        have : ¬ Odd (Rat.floor (8600444322930062324576656 : ℚ)).toNat := by decide
        have h_false : False := this h_odd
        contradiction
      · rintro ⟨m, hm, h_eq⟩
        rcases m with _|m
        · contradiction
        rcases m with _|m
        · omega
        rcases m with _|m
        · omega
        rcases m with _|m
        · omega
        · have : 2^(m+4) = 16 * 2^m := by ring
          omega
    rcases n with _|n
    · -- n = 13
      constructor
      · intro h_odd
        unfold a at h_odd
        rw [a_Q_eq_rec] at h_odd
        repeat (unfold a_Q_rec at h_odd; dsimp only at h_odd)
        unfold a_Q_rec at h_odd
        have h32 : choose 3 2 = 3 := rfl
        have h53 : choose 5 3 = 10 := rfl
        have h74 : choose 7 4 = 35 := rfl
        have h95 : choose 9 5 = 126 := rfl
        have h116 : choose 11 6 = 462 := rfl
        have h137 : choose 13 7 = 1716 := rfl
        have h158 : choose 15 8 = 6435 := rfl
        have h179 : choose 17 9 = 24310 := rfl
        have h1910 : choose 19 10 = 92378 := rfl
        have h2111 : choose 21 11 = 352716 := rfl
        have h2312 : choose 23 12 = 1352078 := rfl
        have h2513 : choose 25 13 = 5200300 := rfl
        rw [h32, h53, h74, h95, h116, h137, h158, h179, h1910, h2111, h2312, h2513] at h_odd
        norm_num at h_odd
        have : ¬ Odd (Rat.floor (1887004503074697406002288128 : ℚ)).toNat := by decide
        have h_false : False := this h_odd
        contradiction
      · rintro ⟨m, hm, h_eq⟩
        rcases m with _|m
        · contradiction
        rcases m with _|m
        · omega
        rcases m with _|m
        · omega
        rcases m with _|m
        · omega
        · have : 2^(m+4) = 16 * 2^m := by ring
          omega
    rcases n with _|n
    · -- n = 14
      constructor
      · intro h_odd
        unfold a at h_odd
        rw [a_Q_eq_rec] at h_odd
        repeat (unfold a_Q_rec at h_odd; dsimp only at h_odd)
        unfold a_Q_rec at h_odd
        have h32 : choose 3 2 = 3 := rfl
        have h53 : choose 5 3 = 10 := rfl
        have h74 : choose 7 4 = 35 := rfl
        have h95 : choose 9 5 = 126 := rfl
        have h116 : choose 11 6 = 462 := rfl
        have h137 : choose 13 7 = 1716 := rfl
        have h158 : choose 15 8 = 6435 := rfl
        have h179 : choose 17 9 = 24310 := rfl
        have h1910 : choose 19 10 = 92378 := rfl
        have h2111 : choose 21 11 = 352716 := rfl
        have h2312 : choose 23 12 = 1352078 := rfl
        have h2513 : choose 25 13 = 5200300 := rfl
        have h2714 : choose 27 14 = 20058300 := rfl
        rw [h32, h53, h74, h95, h116, h137, h158, h179, h1910, h2111, h2312, h2513, h2714] at h_odd
        norm_num at h_odd
        have : ¬ Odd (Rat.floor (418623143412655600699693378816 : ℚ)).toNat := by decide
        have h_false : False := this h_odd
        contradiction
      · rintro ⟨m, hm, h_eq⟩
        rcases m with _|m
        · contradiction
        rcases m with _|m
        · omega
        rcases m with _|m
        · omega
        rcases m with _|m
        · omega
        · have : 2^(m+4) = 16 * 2^m := by ring
          omega
    rcases n with _|n
    · -- n = 15
      constructor
      · intro h_odd
        unfold a at h_odd
        rw [a_Q_eq_rec] at h_odd
        repeat (unfold a_Q_rec at h_odd; dsimp only at h_odd)
        unfold a_Q_rec at h_odd
        have h32 : choose 3 2 = 3 := rfl
        have h53 : choose 5 3 = 10 := rfl
        have h74 : choose 7 4 = 35 := rfl
        have h95 : choose 9 5 = 126 := rfl
        have h116 : choose 11 6 = 462 := rfl
        have h137 : choose 13 7 = 1716 := rfl
        have h158 : choose 15 8 = 6435 := rfl
        have h179 : choose 17 9 = 24310 := rfl
        have h1910 : choose 19 10 = 92378 := rfl
        have h2111 : choose 21 11 = 352716 := rfl
        have h2312 : choose 23 12 = 1352078 := rfl
        have h2513 : choose 25 13 = 5200300 := rfl
        have h2714 : choose 27 14 = 20058300 := rfl
        have h2915 : choose 29 15 = 77558760 := rfl
        rw [h32, h53, h74, h95, h116, h137, h158, h179, h1910, h2111, h2312, h2513, h2714, h2915] at h_odd
        norm_num at h_odd
        have : ¬ Odd (Rat.floor (93762704465298855834523066368000 : ℚ)).toNat := by decide
        have h_false : False := this h_odd
        contradiction
      · rintro ⟨m, hm, h_eq⟩
        rcases m with _|m
        · contradiction
        rcases m with _|m
        · omega
        rcases m with _|m
        · omega
        rcases m with _|m
        · omega
        · have : 2^(m+4) = 16 * 2^m := by ring
          omega
    rcases n with _|n
    · -- n = 16
      constructor
      · intro
        use 4
        decide
      · intro
        unfold a
        rw [a_Q_eq_rec]
        repeat (unfold a_Q_rec; dsimp only)
        unfold a_Q_rec
        have h32 : choose 3 2 = 3 := rfl
        have h53 : choose 5 3 = 10 := rfl
        have h74 : choose 7 4 = 35 := rfl
        have h95 : choose 9 5 = 126 := rfl
        have h116 : choose 11 6 = 462 := rfl
        have h137 : choose 13 7 = 1716 := rfl
        have h158 : choose 15 8 = 6435 := rfl
        have h179 : choose 17 9 = 24310 := rfl
        have h1910 : choose 19 10 = 92378 := rfl
        have h2111 : choose 21 11 = 352716 := rfl
        have h2312 : choose 23 12 = 1352078 := rfl
        have h2513 : choose 25 13 = 5200300 := rfl
        have h2714 : choose 27 14 = 20058300 := rfl
        have h2915 : choose 29 15 = 77558760 := rfl
        have h3116 : choose 31 16 = 300540195 := rfl
        rw [h32, h53, h74, h95, h116, h137, h158, h179, h1910, h2111, h2312, h2513, h2714, h2915, h3116]
        norm_num
        decide
    rcases n with _|n
    · -- n = 17
      constructor
      · intro h_odd
        unfold a at h_odd
        rw [a_Q_eq_rec] at h_odd
        repeat (unfold a_Q_rec at h_odd; dsimp only at h_odd)
        unfold a_Q_rec at h_odd
        have h32 : choose 3 2 = 3 := rfl
        have h53 : choose 5 3 = 10 := rfl
        have h74 : choose 7 4 = 35 := rfl
        have h95 : choose 9 5 = 126 := rfl
        have h116 : choose 11 6 = 462 := rfl
        have h137 : choose 13 7 = 1716 := rfl
        have h158 : choose 15 8 = 6435 := rfl
        have h179 : choose 17 9 = 24310 := rfl
        have h1910 : choose 19 10 = 92378 := rfl
        have h2111 : choose 21 11 = 352716 := rfl
        have h2312 : choose 23 12 = 1352078 := rfl
        have h2513 : choose 25 13 = 5200300 := rfl
        have h2714 : choose 27 14 = 20058300 := rfl
        have h2915 : choose 29 15 = 77558760 := rfl
        have h3116 : choose 31 16 = 300540195 := rfl
        have h3317 : choose 33 17 = 1166803110 := rfl
        rw [h32, h53, h74, h95, h116, h137, h158, h179, h1910, h2111, h2312, h2513, h2714, h2915, h3116, h3317] at h_odd
        norm_num at h_odd
        have : ¬ Odd (Rat.floor (4818612191947640706260755149487263008 : ℚ)).toNat := by decide
        have h_false : False := this h_odd
        contradiction
      · rintro ⟨m, hm, h_eq⟩
        rcases m with _|m
        · contradiction
        rcases m with _|m
        · omega
        rcases m with _|m
        · omega
        rcases m with _|m
        · omega
        rcases m with _|m
        · omega
        · have : 2^(m+5) = 32 * 2^m := by ring
          omega
    · -- n >= 18
      have hn2 : n + 18 ≥ 2 := by omega
      have h_iff := choose_sub_one_div_two_odd_iff (n + 18) hn2
      constructor
      · intro h_odd
        rw [a_odd_iff_choose_odd (n + 18) hn2] at h_odd
        exact h_iff.mp h_odd
      · intro h_pow
        rw [a_odd_iff_choose_odd (n + 18) hn2]
        exact h_iff.mpr h_pow

