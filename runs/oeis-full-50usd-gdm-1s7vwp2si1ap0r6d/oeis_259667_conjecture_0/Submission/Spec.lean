import FormalConjectures.Util.ProblemImports

open Nat Finset

lemma sum_range_symmetric_prod (M : ℕ) : ∀ f : ℕ → ℕ, (∑ i ∈ range (2 * M + 1), f i * f (2 * M - i)) ≡ f M * f M [MOD 2] := by
  induction M with
  | zero =>
    intro f
    simp
    exact Nat.ModEq.refl _
  | succ M ih =>
    intro f
    have h_rw : 2 * (M + 1) = 2 * M + 2 := by omega
    simp_rw [h_rw]
    -- LHS has 2 * M + 2 + 1
    have h_len2 : 2 * M + 2 + 1 = 2 * M + 3 := by omega
    rw [h_len2]
    -- pull out the last term using sum_range_succ
    -- the last term is for i = 2 * M + 2
    have h_last : ∑ i ∈ range (2 * M + 3), f i * f (2 * M + 2 - i) = (∑ i ∈ range (2 * M + 2), f i * f (2 * M + 2 - i)) + f (2 * M + 2) * f 0 := by
      have h1 := sum_range_succ (fun i => f i * f (2 * M + 2 - i)) (2 * M + 2)
      rw [h1]
      congr 2
      have : 2 * M + 2 - (2 * M + 2) = 0 := by omega
      rw [this]
    rw [h_last]
    -- now pull out the first term using sum_range_succ'
    have h_first : ∑ i ∈ range (2 * M + 2), f i * f (2 * M + 2 - i) = f 0 * f (2 * M + 2) + ∑ i ∈ range (2 * M + 1), f (i + 1) * f (2 * M - i + 1) := by
      have h2 := sum_range_succ' (fun i => f i * f (2 * M + 2 - i)) (2 * M + 1)
      have h2_len : 2 * M + 1 + 1 = 2 * M + 2 := by omega
      rw [h2_len] at h2
      have h_zero : 2 * M + 2 - 0 = 2 * M + 2 := by omega
      rw [h_zero] at h2
      have h_sum : (∑ i ∈ range (2 * M + 1), f (i + 1) * f (2 * M + 2 - (i + 1))) = ∑ i ∈ range (2 * M + 1), f (i + 1) * f (2 * M - i + 1) := by
        apply sum_congr rfl
        intro x hx
        congr 2
        have hx_lt := mem_range.mp hx
        omega
      rw [h_sum] at h2
      rw [h2]
      rw [add_comm]
    rw [h_first]
    -- now LHS is (f 0 * f (2 * M + 2) + ∑ i ∈ range (2 * M + 1), f (i + 1) * f (2 * M - i + 1)) + f (2 * M + 2) * f 0
    -- Modulo 2, f 0 * f (2 * M + 2) + f (2 * M + 2) * f 0 is even, so it vanishes.
    -- The remaining term is ∑ i ∈ range (2 * M + 1), f (i + 1) * f (2 * M - i + 1)
    -- Let g i = f (i + 1). Then LHS ≡ ∑ i ∈ range (2 * M + 1), g i * g (2 * M - i)
    -- By induction hypothesis ih on g, this is congruent to g M * g M = f (M + 1) * f (M + 1) [MOD 2].
    have h_mod : (f 0 * f (2 * M + 2) + (∑ i ∈ range (2 * M + 1), f (i + 1) * f (2 * M - i + 1)) + f (2 * M + 2) * f 0) ≡ ∑ i ∈ range (2 * M + 1), f (i + 1) * f (2 * M - i + 1) [MOD 2] := by
      have h_comm : f (2 * M + 2) * f 0 = f 0 * f (2 * M + 2) := by ring
      rw [h_comm]
      -- x + sum + x ≡ sum [MOD 2]
      have : (f 0 * f (2 * M + 2) + (∑ i ∈ range (2 * M + 1), f (i + 1) * f (2 * M - i + 1)) + f 0 * f (2 * M + 2)) = (∑ i ∈ range (2 * M + 1), f (i + 1) * f (2 * M - i + 1)) + 2 * (f 0 * f (2 * M + 2)) := by omega
      rw [this]
      rw [Nat.modEq_iff_dvd]
      simp
    apply Nat.ModEq.trans h_mod
    exact ih (fun i => f (i + 1))

lemma catalan_two_pow_sub_one_odd (k : ℕ) : catalan (2^k - 1) % 2 = 1 := by
  induction k with
  | zero =>
    simp [catalan_zero]
  | succ k ih =>
    -- 2^(k+1) - 1 = 2 * (2^k - 1) + 1
    have h_pow : 2^k ≥ 1 := Nat.one_le_pow k 2 (by omega)
    have h_two_pow : 2^(k + 1) - 1 = 2 * (2^k - 1) + 1 := by omega
    rw [h_two_pow]
    -- catalan (2 * M + 1) = ...
    rw [catalan_succ' (2 * (2^k - 1))]
    rw [Nat.sum_antidiagonal_eq_sum_range_succ (fun x y => catalan x * catalan y)]
    -- now we have ∑ i ∈ range (2 * M + 1), catalan i * catalan (2 * M - i)
    have h_symm := sum_range_symmetric_prod (2^k - 1) catalan
    -- h_symm is ∑ i ∈ range (2 * M + 1), ... ≡ catalan M * catalan M [MOD 2]
    have h_ih_sq : catalan (2^k - 1) * catalan (2^k - 1) ≡ 1 * 1 [MOD 2] := by
      exact Nat.ModEq.mul ih ih
    have h_one : 1 * 1 = 1 := by rfl
    rw [h_one] at h_ih_sq
    exact Nat.ModEq.trans h_symm h_ih_sq

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

theorem choose_two_mul_self_mod_three (c : ℕ) (h : ∃ i, c / 3^i % 3 = 2) : (2 * c).choose c % 3 = 0 := by
  let i := Nat.find h
  have h_digit : c / 3^i % 3 = 2 := Nat.find_spec h
  have h2 : ∀ j < i, c / 3^j % 3 < 2 := by
    intro j hj
    have h_not := Nat.find_min h hj
    have h_mod : c / 3^j % 3 < 3 := Nat.mod_lt _ (by omega)
    omega
  have h_pow_le : 3^i ≤ c := by
    by_contra h_lt
    push_neg at h_lt
    have h_div : c / 3^i = 0 := Nat.div_eq_of_lt h_lt
    rw [h_div] at h_digit
    simp at h_digit
  let a := c + 1
  have h_ca : c < 3^a := by
    have h_pow_self : c < 3^c := Nat.lt_pow_self (by omega : 1 < 3)
    have h_pow_succ : 3^a = 3^c * 3 := by ring
    rw [h_pow_succ]
    omega
  have h_2ca : 2 * c < 3^a := by
    have h_pow_self : c < 3^c := Nat.lt_pow_self (by omega : 1 < 3)
    have h_pow_succ : 3^a = 3^c * 3 := by ring
    rw [h_pow_succ]
    omega
  have h_lt_a : i < a := by
    by_contra h_ge
    push_neg at h_ge
    have h_mono : 3^a ≤ 3^i := Nat.pow_le_pow_right (by omega : 0 < 3) h_ge
    omega
  have h_lucas := Choose.lucas_theorem_nat (p := 3) (n := 2 * c) (k := c) (a := a) h_2ca h_ca
  have h_mem : i ∈ range a := mem_range.mpr h_lt_a
  have h_prod_zero : ∏ j ∈ range a, choose ((2 * c) / 3^j % 3) (c / 3^j % 3) = 0 := by
    apply prod_eq_zero h_mem
    have h_div_two := div_two_mul c i h2
    rw [h_div_two]
    have h_digit_rw : (2 * (c / 3^i)) % 3 = (2 * (c / 3^i % 3)) % 3 := by
      exact Nat.mul_mod 2 (c / 3^i) 3
    rw [h_digit_rw, h_digit]
    simp
  rw [Nat.modEq_iff_dvd] at h_lucas
  have h_dvd : 3 ∣ choose (2 * c) c := by
    omega
  exact Nat.dvd_iff_mod_eq_zero.mp h_dvd

lemma catalan_mod_three (k : ℕ) (h_choose : (2 * (2^k - 1)).choose (2^k - 1) % 3 = 0) : catalan (2^k - 1) % 3 = 0 := by
  have h_mul : 2^k * catalan (2^k - 1) = (2 * (2^k - 1)).choose (2^k - 1) := by
    have h_succ : (2^k - 1) + 1 = 2^k := by
      have : 2^k ≥ 1 := Nat.one_le_pow k 2 (by omega)
      omega
    have h1 := succ_mul_catalan_eq_centralBinom (2^k - 1)
    rw [h_succ] at h1
    rw [centralBinom_eq_two_mul_choose] at h1
    exact h1
  have h_dvd_choose : 3 ∣ (2 * (2^k - 1)).choose (2^k - 1) := Nat.dvd_of_mod_eq_zero h_choose
  rw [← h_mul] at h_dvd_choose
  have h_prime : Nat.Prime 3 := Nat.prime_three
  rcases h_prime.dvd_mul.mp h_dvd_choose with h_dvd_pow | h_dvd_cat
  · have h_dvd_two : 3 ∣ 2 := by
      exact h_prime.dvd_of_dvd_pow h_dvd_pow
    contradiction
  · exact Nat.mod_eq_zero_of_dvd h_dvd_cat


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


lemma four_dvd_three_pow_sub_one (C : ℕ) : 2 ∣ 3^C - 1 := by
  have h_odd : 3^C % 2 = 1 := by
    induction C with
    | zero => rfl
    | succ C ih =>
      rw [pow_succ]
      rw [Nat.mul_mod]
      rw [ih]
  omega

lemma four_pow_mod_three (m : ℕ) : 4^m % 3 = 1 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have h_pow : 4^(m+1) = 4^m * 4 := by ring
    rw [h_pow]
    rw [Nat.mul_mod]
    rw [ih]

lemma even_pow_two_mod_three (j : ℕ) (hj : Even j) : 2^j % 3 = 1 := by
  rcases hj with ⟨m, rfl⟩
  have h_rw : m + m = 2 * m := by omega
  rw [h_rw]
  have h_pow : 2^(2 * m) = 4^m := by
    rw [pow_mul]
    rfl
  rw [h_pow]
  exact four_pow_mod_three m

lemma odd_pow_two_mod_three (j : ℕ) (hj : Odd j) : 2^j % 3 = 2 := by
  rcases hj with ⟨m, rfl⟩
  have h_pow : 2^(2 * m + 1) = 2^(2 * m) * 2 := by
    rw [pow_succ]
  rw [h_pow]
  have h_even : Even (2 * m) := by
    use m
    omega
  have h_mod := even_pow_two_mod_three (2 * m) h_even
  have h_mul_mod : (2^(2 * m) * 2) % 3 = ((2^(2 * m) % 3) * 2) % 3 := by
    exact Nat.mul_mod (2^(2 * m)) 2 3
  rw [h_mul_mod, h_mod]

lemma mod_6_eq_3 (x : ℕ) (h1 : x % 2 = 1) (h2 : x % 3 = 0) : x % 6 = 3 := by
  omega

/--
A259667: Catalan numbers mod 6.
$$a(n) = C_n \bmod 6$$
where $C_n = \frac{1}{n+1} \binom{2n}{n}$ is the $n$-th Catalan number (A000108).
-/
def A259667 (n : ℕ) : ℕ := ((2 * n).choose n / (n + 1)) % 6

/--
It is conjectured that the only k which yield a(2^k-1) = 1 are k = 0, 1 and 5.
Are there other k than 2 and 8 that yield a(2^k-1) = 5?
Otherwise said, is a(2^k-1) = 3 for all k > 8.
-/
theorem A259667_eq_catalan_mod_6 (n : ℕ) : A259667 n = catalan n % 6 := by
  dsimp [A259667]
  rw [catalan_eq_centralBinom_div]
  rw [centralBinom_eq_two_mul_choose]

lemma two_pow_period (i : ℕ) : 2^(2 * 3^i) ≡ 1 [MOD 3^(i+1)] := by
  induction i with
  | zero =>
    rfl
  | succ i ih =>
    have h_rw : 2 * 3^(i+1) = (2 * 3^i) * 3 := by ring
    rw [h_rw, pow_mul]
    have h_mod : 2^(2 * 3^i) % 3^(i+1) = 1 := by
      have h_lt : 1 < 3^(i+1) := by
        have : 3^(i+1) ≥ 3 := @Nat.pow_le_pow_right 3 (by decide : 0 < 3) 1 (i+1) (by omega)
        omega
      have h1 : 1 % 3^(i+1) = 1 := Nat.mod_eq_of_lt h_lt
      rw [Nat.ModEq] at ih
      rw [h1] at ih
      exact ih
    have h_div := Nat.div_add_mod (2^(2 * 3^i)) (3^(i+1))
    have h_eq : 2^(2 * 3^i) = 3^(i+1) * (2^(2 * 3^i) / 3^(i+1)) + 1 := by omega
    rw [h_eq]
    let q := 2^(2 * 3^i) / 3^(i+1)
    have h_poly : (3^(i+1) * q + 1)^3 = 3^(i+2) * (q * (3^i * q * (3^(i+1) * q) + 3^(i+1) * q + 1)) + 1 := by
      have h_pow1 : 3^(i+1) = 3 * 3^i := by
        rw [pow_succ]
        ring
      have h_pow2 : 3^(i+2) = 9 * 3^i := by
        have : i + 2 = i + 1 + 1 := by omega
        rw [this, pow_add]
        ring
      rw [h_pow1, h_pow2]
      generalize 3^i = Z
      ring
    rw [h_poly]
    have h_final : 3^(i+2) * (q * (3^i * q * (3^(i+1) * q) + 3^(i+1) * q + 1)) + 1 ≡ 1 [MOD 3^(i+2)] := by
      rw [Nat.ModEq]
      rw [add_comm]
      rw [Nat.add_mul_mod_self_left]
    exact h_final

lemma two_pow_mod_eq (k r i q : ℕ) (h_eq : k = r + q * (2 * 3^i)) : 2^k ≡ 2^r [MOD 3^(i+1)] := by
  rw [h_eq]
  rw [pow_add 2 r]
  have h_mul_comm : q * (2 * 3^i) = (2 * 3^i) * q := by ring
  rw [h_mul_comm]
  rw [pow_mul]
  have h_base := two_pow_period i
  have h_pow : (2^(2 * 3^i))^q ≡ 1^q [MOD 3^(i+1)] := Nat.ModEq.pow q h_base
  have h_one : 1^q = 1 := by simp
  rw [h_one] at h_pow
  have h_mul := Nat.ModEq.mul_left (2^r) h_pow
  rw [mul_one] at h_mul
  exact h_mul

lemma two_pow_sub_one_mod_eq (k r i q : ℕ) (h_eq : k = r + q * (2 * 3^i)) : (2^k - 1) % 3^(i+1) = (2^r - 1) % 3^(i+1) := by
  have h_mod := two_pow_mod_eq k r i q h_eq
  have h_div_k := Nat.div_add_mod (2^k) (3^(i+1))
  have h_div_r := Nat.div_add_mod (2^r) (3^(i+1))
  have h_not_dvd_k : 3^(i+1) ∣ 2^k → False := by
    intro hd
    have h_prime : Nat.Prime 3 := Nat.prime_three
    have h_dvd_pow : 3 ∣ 2^k := by
      have h_dvd_three : 3 ∣ 3^(i+1) := by
        use 3^i
        ring
      exact Nat.dvd_trans h_dvd_three hd
    have h_dvd_two : 3 ∣ 2 := h_prime.dvd_of_dvd_pow h_dvd_pow
    contradiction
  have h_not_dvd_r : 3^(i+1) ∣ 2^r → False := by
    intro hd
    have h_prime : Nat.Prime 3 := Nat.prime_three
    have h_dvd_three : 3 ∣ 3^(i+1) := by
      use 3^i
      ring
    have h_dvd_2r : 3 ∣ 2^r := Nat.dvd_trans h_dvd_three hd
    have h_dvd_2 : 3 ∣ 2 := h_prime.dvd_of_dvd_pow h_dvd_2r
    contradiction
  have h_rem_nz_k : 2^k % 3^(i+1) ≠ 0 := by
    intro hc
    have := Nat.dvd_of_mod_eq_zero hc
    exact h_not_dvd_k this
  have h_rem_nz_r : 2^r % 3^(i+1) ≠ 0 := by
    intro hc
    have : 3^(i+1) ∣ 2^r := Nat.dvd_of_mod_eq_zero hc
    exact h_not_dvd_r this
  have h_eq_mul_k : 2^k = (2^k / 3^(i+1)) * 3^(i+1) + 2^k % 3^(i+1) := by
    have h_comm : 3^(i+1) * (2^k / 3^(i+1)) = (2^k / 3^(i+1)) * 3^(i+1) := by ring
    rw [h_comm] at h_div_k
    exact h_div_k.symm
  have h_eq_mul_r : 2^r = (2^r / 3^(i+1)) * 3^(i+1) + 2^r % 3^(i+1) := by
    have h_comm : 3^(i+1) * (2^r / 3^(i+1)) = (2^r / 3^(i+1)) * 3^(i+1) := by ring
    rw [h_comm] at h_div_r
    exact h_div_r.symm
  have h_rem_ge_k : 2^k % 3^(i+1) ≥ 1 := Nat.pos_of_ne_zero h_rem_nz_k
  have h_rem_ge_r : 2^r % 3^(i+1) ≥ 1 := Nat.pos_of_ne_zero h_rem_nz_r
  have h_rw_k : 2^k - 1 = (2^k / 3^(i+1)) * 3^(i+1) + (2^k % 3^(i+1) - 1) := by omega
  have h_rw_r : 2^r - 1 = (2^r / 3^(i+1)) * 3^(i+1) + (2^r % 3^(i+1) - 1) := by omega
  rw [h_rw_k, h_rw_r]
  rw [add_comm (2^k / 3^(i+1) * 3^(i+1))]
  rw [add_comm (2^r / 3^(i+1) * 3^(i+1))]
  rw [Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right]
  have h_lt_k : 2^k % 3^(i+1) - 1 < 3^(i+1) := by
    have : 2^k % 3^(i+1) < 3^(i+1) := Nat.mod_lt _ (by positivity)
    omega
  have h_lt_r : 2^r % 3^(i+1) - 1 < 3^(i+1) := by
    have : 2^r % 3^(i+1) < 3^(i+1) := Nat.mod_lt _ (by positivity)
    omega
  rw [Nat.mod_eq_of_lt h_lt_k, Nat.mod_eq_of_lt h_lt_r]
  rw [Nat.ModEq] at h_mod
  rw [h_mod]

lemma mod_mul_div_self_eq (a b c : ℕ) (hb : b > 0) : a % (b * c) / b = (a / b) % c := by
  by_cases hc : c = 0
  · rw [hc]
    simp
  · have hc_pos : c > 0 := Nat.pos_of_ne_zero hc
    have h_mul_pos : b * c > 0 := Nat.mul_pos hb hc_pos
    have h_div_add_mod : a = (b * c) * (a / (b * c)) + a % (b * c) := (Nat.div_add_mod a (b * c)).symm
    have h_rem_lt : a % (b * c) < b * c := Nat.mod_lt a h_mul_pos
    have h_rw : a / b = ((a % (b * c)) + b * (c * (a / (b * c)))) / b := by
      nth_rewrite 1 [h_div_add_mod]
      congr 1
      ring
    rw [h_rw]
    rw [Nat.add_mul_div_left (a % (b * c)) (c * (a / (b * c))) hb]
    rw [Nat.add_mul_mod_self_left]
    have h_lt : a % (b * c) / b < c := by
      exact Nat.div_lt_of_lt_mul h_rem_lt
    exact (Nat.mod_eq_of_lt h_lt).symm

lemma digit_periodic (k r i q : ℕ) (h_eq : k = r + q * (2 * 3^i)) : (2^k - 1) / 3^i % 3 = (2^r - 1) / 3^i % 3 := by
  have h_mod := two_pow_sub_one_mod_eq k r i q h_eq
  have h_digit (X : ℕ) : X / 3^i % 3 = (X % 3^(i+1)) / 3^i := by
    have h_pow : 3^(i+1) = 3^i * 3 := by
      rw [pow_succ]
    have h_pow_pos : 3^i > 0 := Nat.pos_of_ne_zero (pow_ne_zero i (by omega))
    rw [h_pow]
    rw [mod_mul_div_self_eq X (3^i) 3 h_pow_pos]
  rw [h_digit (2^k - 1), h_digit (2^r - 1)]
  rw [h_mod]



lemma oeis_259667_part3 (k : ℕ) (hk : k > 8) (h_two : ∃ i, (2^k - 1) / 3^i % 3 = 2) : A259667 (2^k - 1) = 3 := by
  have h_odd := catalan_two_pow_sub_one_odd k
  have h_choose := choose_two_mul_self_mod_three (2^k - 1) h_two
  have h_mod3 := catalan_mod_three k h_choose
  have h_mod6 := mod_6_eq_3 (catalan (2^k - 1)) h_odd h_mod3
  rw [A259667_eq_catalan_mod_6, h_mod6]


lemma pow_three_gt_self (x : ℕ) : 3^x > x := by
  induction x with
  | zero => omega
  | succ x ih =>
    have : 3^(x+1) = 3^x * 3 := by ring
    omega

lemma exists_m (j : ℕ) (hj : j ≥ 3) : ∃ m, 3^m < 2^(j+1) ∧ 2^(j+1) ≤ 3^(m+1) := by
  let P := fun x => 3^x < 2^(j+1)
  let n := 2^(j+1)
  let m := Nat.findGreatest P n
  use m
  have h_eq_iff : Nat.findGreatest P n = m ↔ m ≤ n ∧ (m ≠ 0 → P m) ∧ ∀ ⦃x⦄, m < x → x ≤ n → ¬P x := Nat.findGreatest_eq_iff
  have h_m_eq : Nat.findGreatest P n = m := rfl
  rw [h_m_eq] at h_eq_iff
  have h_spec := h_eq_iff.mp rfl
  rcases h_spec with ⟨hm_le, hm_prop, h_greatest⟩
  have h_P0 : P 0 := by
    dsimp [P]
    have h_pow : 2^(j+1) ≥ 2^4 := Nat.pow_le_pow_right (by omega : 0 < 2) (by omega)
    have : 2^4 = 16 := by rfl
    omega
  have h_Pm : P m := by
    by_cases h : m = 0
    · rw [h]
      exact h_P0
    · exact hm_prop h
  refine ⟨h_Pm, ?_⟩
  have h_m_lt_n : m < n := by
    by_contra h_ge
    have h_eq : m = n := by omega
    have h_Pn : P n := by
      rw [← h_eq]
      exact h_Pm
    change 3^n < n at h_Pn
    have h_gt := pow_three_gt_self n
    omega
  have h_not_P : ¬ P (m + 1) := by
    apply h_greatest (by omega) (by omega)
  change ¬ (3^(m+1) < 2^(j+1)) at h_not_P
  omega

lemma div_from_equation (u m : ℕ) (h_eq : 2 * (u % 3^m) = 3^m - 1) : 3^m ∣ 2 * u + 1 := by
  have h_div_add : u = 3^m * (u / 3^m) + u % 3^m := (Nat.div_add_mod u (3^m)).symm
  have h_mul : 2 * u + 1 = 2 * (3^m * (u / 3^m) + u % 3^m) + 1 := by
    nth_rewrite 1 [h_div_add]
    rfl
  have h_ring : 2 * (3^m * (u / 3^m) + u % 3^m) + 1 = 3^m * (2 * (u / 3^m)) + (2 * (u % 3^m) + 1) := by ring
  rw [h_ring] at h_mul
  rw [h_eq] at h_mul
  have h_sub : 3^m - 1 + 1 = 3^m := by
    have : 3^m ≥ 1 := Nat.one_le_pow m 3 (by omega)
    omega
  rw [h_sub] at h_mul
  have h_ring2 : 3^m * (2 * (u / 3^m)) + 3^m = 3^m * (2 * (u / 3^m) + 1) := by ring
  rw [h_ring2] at h_mul
  rw [h_mul]
  exact Nat.dvd_mul_right (3^m) (2 * (u / 3^m) + 1)

lemma three_pow_mod_eight (m : ℕ) : 3^m % 8 = 1 ∨ 3^m % 8 = 3 := by
  induction m with
  | zero => left; rfl
  | succ m ih =>
    rcases ih with h1 | h3
    · right
      have : 3^(m+1) = 3^m * 3 := by ring
      rw [this, Nat.mul_mod, h1]
    · left
      have : 3^(m+1) = 3^m * 3 := by ring
      rw [this, Nat.mul_mod, h3]

lemma two_pow_mod_eight (n : ℕ) (hn : n ≥ 3) : 2^n % 8 = 0 := by
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    have : 2^(n+1) = 2^n * 2 := by ring
    rw [this, Nat.mul_mod, ih]

lemma power_equation_impossible (j m : ℕ) (hj : j ≥ 3) (heq : 2^(j+1) - 3^m = 1) : False := by
  have h_two_pow : 2^(j+1) % 8 = 0 := by
    apply two_pow_mod_eight (j+1)
    omega
  have h_three_pow := three_pow_mod_eight m
  have h_eq_add : 2^(j+1) = 3^m + 1 := by omega
  have h_mod : 2^(j+1) % 8 = (3^m + 1) % 8 := by rw [h_eq_add]
  rw [h_two_pow] at h_mod
  rcases h_three_pow with h1 | h3
  · have h_mod_add : (3^m + 1) % 8 = (3^m % 8 + 1) % 8 := Nat.add_mod (3^m) 1 8
    rw [h_mod_add, h1] at h_mod
    contradiction
  · have h_mod_add : (3^m + 1) % 8 = (3^m % 8 + 1) % 8 := Nat.add_mod (3^m) 1 8
    rw [h_mod_add, h3] at h_mod
    contradiction

lemma case_two_contradiction (j : ℕ) (hj : j ≥ 3) (hc1 : ∀ m, (2^j - 1) / 3^m % 3 < 2) (hc2 : ∀ m, (2^(j+1) - 1) / 3^m % 3 < 2) : False := by
  let u := 2^j - 1
  have h_u : 2^(j+1) - 1 = 2 * u + 1 := by
    have : 2^(j+1) = 2^j * 2 := by ring
    have : 2^j ≥ 1 := Nat.one_le_pow j 2 (by omega)
    omega
  have hc2' : ∀ m, (2 * u + 1) / 3^m % 3 < 2 := by
    rw [← h_u]
    exact hc2
  obtain ⟨m, h_lt, h_ge⟩ := exists_m j hj
  have h_or := cantor_two_mul_add_one u hc1 hc2' m
  rcases h_or with h_or_lt | h_or_eq
  · have : 3^m - 1 ≤ 2 * u := by
      have : 2 * u = 2^(j+1) - 2 := by
        have : 2^(j+1) = 2^j * 2 := by ring
        have : 2^j ≥ 1 := Nat.one_le_pow j 2 (by omega)
        omega
      omega
    omega
  · have h_dvd := div_from_equation u m h_or_eq
    rw [← h_u] at h_dvd
    rcases h_dvd with ⟨q, hq⟩
    have h_q_lt : q < 3 := by
      have h_pow : 3^(m+1) = 3 * 3^m := by ring
      rw [h_pow] at h_ge
      have h_mul_lt : 3^m * q < 3^m * 3 := by omega
      by_contra h_ge3
      push_neg at h_ge3
      have h_mono : 3^m * q ≥ 3^m * 3 := Nat.mul_le_mul_left (3^m) h_ge3
      omega
    have h_q_gt : q > 0 := by
      by_contra h_zero
      push_neg at h_zero
      have : q = 0 := by omega
      rw [this] at hq
      omega
    have h_q_cases : q = 1 ∨ q = 2 := by omega
    rcases h_q_cases with rfl | rfl
    · have : 2^(j+1) - 3^m = 1 := by omega
      exact power_equation_impossible j m hj this
    · have h_odd : (2^(j+1) - 1) % 2 = 1 := by
        have h_pow : 2^(j+1) = 2^j * 2 := by ring
        have h_ge : 2^j ≥ 1 := Nat.one_le_pow j 2 (by omega)
        have h_eq : 2^(j+1) - 1 = 2 * (2^j - 1) + 1 := by omega
        rw [h_eq]
        omega
      have h_even : (3^m * 2) % 2 = 0 := by
        rw [mul_comm]
        omega
      have h_mod_eq : (2^(j+1) - 1) % 2 = (3^m * 2) % 2 := by rw [hq]
      rw [h_odd, h_even] at h_mod_eq
      contradiction

lemma div_add_one_eq (n m : ℕ) (hn : n % 3 = 0) : (n + 1) / 3^(m+1) = n / 3^(m+1) := by
  have h_dvd : 3 ∣ 3^(m+1) := by
    use 3^m
    ring
  have h_mod : n % 3^(m+1) % 3 = 0 := by
    rw [Nat.mod_mod_of_dvd n h_dvd, hn]
  have h_pos : 3^(m+1) > 0 := Nat.pos_of_ne_zero (pow_ne_zero (m+1) (by omega))
  have h_lt : n % 3^(m+1) < 3^(m+1) := Nat.mod_lt n h_pos
  have h_rem_lt : n % 3^(m+1) + 1 < 3^(m+1) := by
    by_contra h_ge
    push_neg at h_ge
    have h_eq : n % 3^(m+1) + 1 = 3^(m+1) := by omega
    have h_rem_eq : n % 3^(m+1) = 3^(m+1) - 1 := by omega
    have h_rem_mod : (n % 3^(m+1)) % 3 = (3^(m+1) - 1) % 3 := by rw [h_rem_eq]
    have h_pow_succ : 3^(m+1) = 3 * 3^m := by ring
    have h_sub_mod : (3^(m+1) - 1) % 3 = 2 := by
      rw [h_pow_succ]
      generalize hX : 3^m = X
      have hX_pos : X ≥ 1 := by
        rw [← hX]
        exact Nat.one_le_pow m 3 (by omega)
      have h_eq2 : 3 * X - 1 = 3 * (X - 1) + 2 := by omega
      rw [h_eq2]
      have h_eq3 : (3 * (X - 1) + 2) = 2 + 3 * (X - 1) := by ring
      rw [h_eq3]
      rw [Nat.add_mul_mod_self_left]
    rw [h_mod, h_sub_mod] at h_rem_mod
    contradiction
  have h_div_add : (n + 1) = (n / 3^(m+1)) * 3^(m+1) + (n % 3^(m+1) + 1) := by
    have h1 := Nat.div_add_mod' n (3^(m+1))
    omega
  rw [h_div_add]
  have h_rw : (n / 3^(m+1) * 3^(m+1) + (n % 3^(m+1) + 1)) = (n % 3^(m+1) + 1) + 3^(m+1) * (n / 3^(m+1)) := by ring
  rw [h_rw]
  rw [Nat.add_mul_div_left (n % 3^(m+1) + 1) (n / 3^(m+1)) h_pos]
  have h_zero : (n % 3^(m+1) + 1) / 3^(m+1) = 0 := Nat.div_eq_of_lt h_rem_lt
  rw [h_zero]
  simp

lemma consecutive_not_cantor (j : ℕ) (hj : j ≥ 2) (hc1 : ∀ m, (2^j - 1) / 3^m % 3 < 2) (hc2 : ∀ m, (2^(j+1) - 1) / 3^m % 3 < 2) : False := by
  have h_or_even_odd : Even j ∨ Odd j := Nat.even_or_odd j
  rcases h_or_even_odd with h_even | h_odd
  · have h_mod : 2^j % 3 = 1 := even_pow_two_mod_three j h_even
    have h_div_zero : (2^j - 1) % 3 = 0 := by
      have : 2^j ≥ 1 := Nat.one_le_pow j 2 (by omega)
      omega
    let x := 2^j - 1
    have hx_ge_one : x ≥ 1 := by
      have : 2^j ≥ 4 := Nat.pow_le_pow_right (by omega : 0 < 2) hj
      omega
    have h_div3 : 2 * (x / 3) = (2 * x) / 3 := by
      have h_digit : x / 3^0 % 3 < 2 := by
        rw [pow_zero, Nat.div_one]
        rw [h_div_zero]
        omega
      have h_h2 : ∀ k < 1, x / 3^k % 3 < 2 := by
        intro k hk
        have : k = 0 := by omega
        rw [this]
        exact h_digit
      exact (div_two_mul x 1 h_h2).symm
    have h_cantor_x : ∀ m, (x / 3) / 3^m % 3 < 2 := by
      intro m
      have h_div_step : (x / 3) / 3^m = x / 3^(m+1) := by
        have h_pow_succ : 3^(m+1) = 3 * 3^m := by ring
        rw [h_pow_succ]
        exact Nat.div_div_eq_div_mul x 3 (3^m)
      rw [h_div_step]
      exact hc1 (m+1)
    have h_cantor_2x : ∀ m, (2 * (x / 3)) / 3^m % 3 < 2 := by
      intro m
      rw [h_div3]
      have h_div_step : ((2 * x) / 3) / 3^m = (2 * x) / 3^(m+1) := by
        have h_pow_succ : 3^(m+1) = 3 * 3^m := by ring
        rw [h_pow_succ]
        exact Nat.div_div_eq_div_mul (2 * x) 3 (3^m)
      rw [h_div_step]
      have h_mod3 : (2 * x) % 3 = 0 := by
        rw [Nat.mul_mod]
        rw [h_div_zero]
      have h_eq_div : (2 * x) / 3^(m+1) = (2 * x + 1) / 3^(m+1) := by
        exact (div_add_one_eq (2 * x) m h_mod3).symm
      rw [h_eq_div]
      have h_rw2 : 2 * x + 1 = 2^(j+1) - 1 := by
        have h_pow : 2^(j+1) = 2^j * 2 := by ring
        omega
      rw [h_rw2]
      exact hc2 (m+1)
    have h_w_ge_one : x / 3 ≥ 1 := by omega
    exact cantor_two_mul_impossible (x / 3) h_w_ge_one h_cantor_x h_cantor_2x
  · rcases h_odd with ⟨m, rfl⟩
    have hj3 : 2 * m + 1 ≥ 3 := by omega
    exact case_two_contradiction (2 * m + 1) hj3 hc1 hc2

lemma A259667_odd (k : ℕ) : A259667 (2^k - 1) = 1 ∨ A259667 (2^k - 1) = 3 ∨ A259667 (2^k - 1) = 5 := by
  have h_eq := A259667_eq_catalan_mod_6 (2^k - 1)
  have h_odd := catalan_two_pow_sub_one_odd k
  have h_lt : A259667 (2^k - 1) < 6 := by
    rw [h_eq]
    exact Nat.mod_lt _ (by decide)
  have h_mod2 : A259667 (2^k - 1) % 2 = 1 := by
    rw [h_eq]
    have h_dvd : 2 ∣ 6 := by decide
    rw [Nat.mod_mod_of_dvd _ h_dvd, h_odd]
  omega
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000


theorem oeis_259667_conjecture_0 :
    (∀ k : ℕ, A259667 (2^k - 1) = 1 ↔ k = 0 ∨ k = 1 ∨ k = 5) ∧
    (∀ k : ℕ, A259667 (2^k - 1) = 5 ↔ k = 2 ∨ k = 8) ∧
    (∀ k : ℕ, k > 8 → A259667 (2^k - 1) = 3) := by
  refine ⟨fun k ↦ ?_, fun k ↦ ?_, fun k hk ↦ ?_⟩
  · have h : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k > 8 := by omega
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hk
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · constructor <;> intro hk_eq
      · have h_part3 : A259667 (2^k - 1) = 3 := sorry
        rw [h_part3] at hk_eq
        contradiction
      · rcases hk_eq with rfl | rfl | rfl <;> omega
  · have h : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k > 8 := by omega
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hk
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · constructor <;> intro hk_eq
      · have h_part3 : A259667 (2^k - 1) = 3 := sorry
        rw [h_part3] at hk_eq
        contradiction
      · rcases hk_eq with rfl | rfl <;> omega
  · sorry

