import FormalConjectures.Util.ProblemImports

open Nat Finset

def A259667 (n : ℕ) : ℕ := ((2 * n).choose n / (n + 1)) % 6


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
  have h_div := Nat.div_add_mod c (3^i) -- Wait, div_add_mod says (c / d) * d + c % d = c ? Or is it (c / d) * d + c % d = c ? Let us keep div_add_mod or similar
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
  -- Choose.lucas_theorem_nat says choose (2 * c) c ≡ ∏ j ∈ range a, choose ((2 * c) / 3^j % 3) (c / 3^j % 3) [MOD 3]
  -- We know i < a, so i ∈ range a.
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

theorem my_test_thm (k : ℕ) (hk : k > 8) : A259667 (2^k - 1) = 3 := answer(sorry)



