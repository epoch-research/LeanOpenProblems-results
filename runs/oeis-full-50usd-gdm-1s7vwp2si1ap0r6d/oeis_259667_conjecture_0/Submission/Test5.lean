import FormalConjectures.Util.ProblemImports

open Nat

lemma remainder_lt_half_pow (c : ℕ) (i : ℕ) (h2 : ∀ j < i, c / 3^j % 3 < 2) : 2 * (c % 3^i) < 3^i := by
  induction i with
  | zero =>
    rw [pow_zero, Nat.mod_one]
    omega
  | succ i ih =>
    have h2_i : ∀ j < i, c / 3^j % 3 < 2 := by
      intro j hj
      apply h2 j
      omega
    have ih' := ih h2_i
    rw [mod_pow_succ]
    have h_digit : c / 3^i % 3 < 2 := by
      apply h2 i
      omega
    have h_or : c / 3^i % 3 = 0 ∨ c / 3^i % 3 = 1 := by omega
    rcases h_or with h_zero | h_one
    · rw [h_zero]
      simp
      omega
    · rw [h_one]
      simp
      omega

lemma div_two_mul (c : ℕ) (i : ℕ) (h2 : ∀ j < i, c / 3^j % 3 < 2) : (2 * c) / 3^i = 2 * (c / 3^i) := by
  have h_bound := remainder_lt_half_pow c i h2
  have h_div_add_mod : (c / 3^i) * 3^i + c % 3^i = c := by
    exact Nat.div_add_mod' c (3^i)
  generalize h_pow : 3^i = d
  rw [h_pow] at h_bound h_div_add_mod
  have h_pos : d > 0 := by
    rw [← h_pow]
    exact Nat.pos_of_ne_zero (pow_ne_zero i (by omega))
  generalize h_q : c / d = q
  generalize h_r : c % d = r
  rw [h_q, h_r] at h_div_add_mod
  rw [h_r] at h_bound
  rw [← h_div_add_mod]
  have h_ring : 2 * (q * d + r) = 2 * r + d * (2 * q) := by ring
  rw [h_ring]
  rw [Nat.add_mul_div_left (2 * r) (2 * q) h_pos]
  have h_zero : (2 * r) / d = 0 := Nat.div_eq_of_lt h_bound
  rw [h_zero]
  simp

lemma cantor_two_mul_impossible (x : ℕ) (hx : x ≥ 1) (hc1 : ∀ j, x / 3^j % 3 < 2) (hc2 : ∀ j, (2 * x) / 3^j % 3 < 2) : False := by
  have h_exists : ∃ j, x < 3^j := by
    use x + 1
    have h_pow_self : x < 3^x := Nat.lt_pow_self (by omega : 1 < 3)
    have h_pow_succ : 3^(x+1) = 3^x * 3 := by ring
    rw [h_pow_succ]
    omega
  let a := Nat.find h_exists
  have h_lt_a : x < 3^a := Nat.find_spec h_exists
  have h_a_pos : a > 0 := by
    by_contra h_zero
    have : a = 0 := by omega
    rw [this] at h_lt_a
    simp at h_lt_a
    omega
  let c := a - 1
  have h_succ : a = c + 1 := by omega
  have h_lt_succ : x < 3^c * 3 := by
    have h_rw := h_lt_a
    rw [h_succ, pow_succ] at h_rw
    exact h_rw
  have h_ge_c : 3^c ≤ x := by
    have h_min := Nat.find_min h_exists (by omega : c < a)
    push_neg at h_min
    exact h_min
  -- so 3^c ≤ x < 3^(c+1)
  -- so x / 3^c ≥ 1 and x / 3^c < 3
  have h_pos_3c : 3^c > 0 := by exact Nat.pos_of_ne_zero (pow_ne_zero c (by omega))
  -- Let us just use omega to prove x / 3^c ≥ 1
  have h_div_ge : x / 3^c ≥ 1 := by
    change 1 ≤ x / 3^c
    rw [Nat.le_div_iff_mul_le h_pos_3c]
    simp
    exact h_ge_c
  have h_div_lt : x / 3^c < 3 := by
    exact Nat.div_lt_of_lt_mul h_lt_succ
  have h_mod_eq : x / 3^c % 3 = x / 3^c := Nat.mod_eq_of_lt h_div_lt
  have h_hc1_c : x / 3^c % 3 < 2 := hc1 c
  rw [h_mod_eq] at h_hc1_c
  have h_div_eq_one : x / 3^c = 1 := by omega
  have h_mod_one : x / 3^c % 3 = 1 := by rw [h_div_eq_one]
  -- now apply div_two_mul
  have h_h2 : ∀ j < c, x / 3^j % 3 < 2 := by
    intro j hj
    apply hc1 j
  have h_div_two := div_two_mul x c h_h2
  have h_hc2_c : (2 * x) / 3^c % 3 < 2 := hc2 c
  rw [h_div_two] at h_hc2_c
  rw [h_div_eq_one] at h_hc2_c
  omega

lemma cantor_two_mul_add_one (u : ℕ) (hc1 : ∀ m, u / 3^m % 3 < 2) (hc2 : ∀ m, (2 * u + 1) / 3^m % 3 < 2) :
    ∀ j, 2 * u < 3^j - 1 ∨ 2 * (u % 3^j) = 3^j - 1 := by
  intro j
  induction j with
  | zero =>
    right
    have : u % 1 = 0 := Nat.mod_one u
    omega
  | succ j ih =>
    rcases ih with h_lt | h_eq
    · left
      have h_pow : 3^(j+1) = 3^j * 3 := by ring
      have h_lt_pow : 3^j < 3^(j+1) := by
        rw [h_pow]
        have : 3^j > 0 := Nat.pos_of_ne_zero (pow_ne_zero j (by omega))
        omega
      omega
    · let d := u / 3^j % 3
      have h_d_lt : d < 3 := Nat.mod_lt _ (by omega)
      have h_cantor : d < 2 := hc1 j
      have h_d_cases : d = 0 ∨ d = 1 := by omega
      rcases h_d_cases with hd0 | hd1
      · -- d = 0
        have h_mod_step : u % 3^(j+1) = u % 3^j := by
          rw [mod_pow_succ]
          have : u / 3^j % 3 = d := rfl
          rw [this, hd0]
          simp
        let q := u / 3^j
        have h_q_eq : q = u / 3^j := rfl
        have h_q_mod : q % 3 = 0 := by
          change u / 3^j % 3 = 0 at hd0
          exact hd0
        have h_q_div : q = 3 * (q / 3) := by
          omega
        let w := q / 3
        have h_w_eq : w = q / 3 := rfl
        have h_w_cases : w = 0 ∨ w ≥ 1 := by omega
        rcases h_w_cases with hw0 | hw1
        · -- w = 0
          have h_q0 : q = 0 := by omega
          have h_div0 : u / 3^j = 0 := h_q0
          have h_or := Nat.div_eq_zero_iff.mp h_div0
          rcases h_or with h_pow0 | h_lt
          · have : 3^j > 0 := Nat.pos_of_ne_zero (pow_ne_zero j (by omega))
            omega
          · have h_mod_u : u % 3^j = u := Nat.mod_eq_of_lt h_lt
            left
            rw [h_mod_u] at h_eq
            have h_pow : 3^(j+1) = 3^j * 3 := by ring
            have : 3^j > 0 := Nat.pos_of_ne_zero (pow_ne_zero j (by omega))
            omega
        · -- w >= 1
          -- we will show cantor_two_mul_impossible w leads to False
          have h_u_decomp : u = 3 * w * 3^j + u % 3^j := by
            have := Nat.div_add_mod' u (3^j)
            rw [← this]
            congr 2
            omega
          have h_two_u : 2 * u = 6 * w * 3^j + 2 * (u % 3^j) := by
            nth_rewrite 1 [h_u_decomp]
            ring
          have h_pow_pos : 3^j ≥ 1 := Nat.one_le_pow j 3 (by omega)
          have h_two_u_add_one : 2 * u + 1 = (6 * w + 1) * 3^j := by
            rw [h_two_u, h_eq]
            have h_sub : 6 * w * 3^j + (3^j - 1) + 1 = 6 * w * 3^j + (3^j - 1 + 1) := by ring
            rw [h_sub]
            rw [Nat.sub_add_cancel h_pow_pos]
            ring
          have h_div_two_u : (2 * u + 1) / 3^(j+1) = 2 * w := by
            have h_pow_succ : 3^(j+1) = 3^j * 3 := by ring
            rw [h_pow_succ]
            have h_div_step : (2 * u + 1) / (3^j * 3) = ((2 * u + 1) / 3^j) / 3 := by
              exact (Nat.div_div_eq_div_mul (2 * u + 1) (3^j) 3).symm
            rw [h_div_step, h_two_u_add_one]
            have h_div_self : (6 * w + 1) * 3^j / 3^j = 6 * w + 1 := by
              have h_pos : 3^j > 0 := Nat.pos_of_ne_zero (pow_ne_zero j (by omega))
              exact Nat.mul_div_cancel (6 * w + 1) h_pos
            rw [h_div_self]
            omega
          have h_div_u : u / 3^(j+1) = w := by
            have h_pow_succ : 3^(j+1) = 3^j * 3 := by ring
            rw [h_pow_succ]
            have h_div_step : u / (3^j * 3) = (u / 3^j) / 3 := by
              exact (Nat.div_div_eq_div_mul u (3^j) 3).symm
            rw [h_div_step]
          have h_cantor_w1 : ∀ m, w / 3^m % 3 < 2 := by
            intro m
            have h_div_step : w / 3^m = u / 3^(j + 1 + m) := by
              rw [← h_div_u]
              have h_pow_add : 3^(j + 1 + m) = 3^(j+1) * 3^m := pow_add 3 (j+1) m
              rw [h_pow_add]
              exact Nat.div_div_eq_div_mul u (3^(j+1)) (3^m)
            rw [h_div_step]
            exact hc1 (j + 1 + m)
          have h_cantor_w2 : ∀ m, (2 * w) / 3^m % 3 < 2 := by
            intro m
            have h_div_step : (2 * w) / 3^m = (2 * u + 1) / 3^(j + 1 + m) := by
              rw [← h_div_two_u]
              have h_pow_add : 3^(j + 1 + m) = 3^(j+1) * 3^m := pow_add 3 (j+1) m
              rw [h_pow_add]
              exact Nat.div_div_eq_div_mul (2 * u + 1) (3^(j+1)) (3^m)
            rw [h_div_step]
            exact hc2 (j + 1 + m)
          have h_false : False := cantor_two_mul_impossible w hw1 h_cantor_w1 h_cantor_w2
          contradiction
      · -- d = 1
        right
        rw [mod_pow_succ]
        have : u / 3^j % 3 = d := rfl
        rw [this, hd1]
        have h_pow : 3^(j+1) = 3^j * 3 := by ring
        omega
