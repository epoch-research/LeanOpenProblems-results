import FormalConjectures.Util.ProblemImports

open Nat Finset

def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range n) fun k ↦
    (2 ^ Nat.choose (k + 1) 2) *
    (Finset.prod (Finset.Ico (k + 1) n) fun j ↦ (2 ^ j - 1))

theorem a_succ (n : ℕ) : a (n + 1) = 2 ^ Nat.choose (n + 1) 2 + (2 ^ n - 1) * a n := by
  dsimp [a]
  rw [sum_range_succ]
  have h_last : (2 ^ Nat.choose (n + 1) 2) * ∏ j ∈ Ico (n + 1) (n + 1), (2 ^ j - 1) = 2 ^ Nat.choose (n + 1) 2 := by
    simp
  rw [h_last, add_comm]
  congr 1
  have h_sum : ∑ k ∈ range n, 2 ^ Nat.choose (k + 1) 2 * ∏ j ∈ Ico (k + 1) (n + 1), (2 ^ j - 1) =
                ∑ k ∈ range n, (2 ^ n - 1) * (2 ^ Nat.choose (k + 1) 2 * ∏ j ∈ Ico (k + 1) n, (2 ^ j - 1)) := by
    apply sum_congr rfl
    intro k hk
    have hk_lt : k < n := mem_range.mp hk
    have h_prod : ∏ j ∈ Ico (k + 1) (n + 1), (2 ^ j - 1) = (∏ j ∈ Ico (k + 1) n, (2 ^ j - 1)) * (2 ^ n - 1) := by
      apply prod_Ico_succ_top hk_lt
    rw [h_prod]
    ring
  rw [h_sum]
  rw [← mul_sum]

theorem coprime_two_of_prime_of_ne_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : Nat.Coprime 2 p := by
  have h_dvd : ¬ 2 ∣ p := by
    intro h
    cases hp.eq_one_or_self_of_dvd 2 h with
    | inl h1 => contradiction
    | inr h2 => exact hp2 h2.symm
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h_dvd

theorem pow_two_p_minus_one_mod {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
  (2 ^ (2 * (p - 1))) % p = 1 % p := by
  have h_fermat : 2 ^ (p - 1) % p = 1 % p := Nat.ModEq.pow_card_sub_one_eq_one hp (coprime_two_of_prime_of_ne_two hp hp2)
  have h_pow : 2 ^ (2 * (p - 1)) = (2 ^ (p - 1)) ^ 2 := by
    rw [mul_comm, pow_mul]
  rw [h_pow, Nat.pow_mod, h_fermat, ← Nat.pow_mod]

theorem choose_two_p_minus_one_succ (p : ℕ) :
  Nat.choose (2 * (p - 1) + 1) 2 = (2 * (p - 1) + 1) * (p - 1) := by
  rw [choose_two_right]
  have h1 : 2 * (p - 1) + 1 - 1 = 2 * (p - 1) := by omega
  rw [h1]
  have h2 : (2 * (p - 1) + 1) * (2 * (p - 1)) = 2 * ((2 * (p - 1) + 1) * (p - 1)) := by ring
  rw [h2]
  exact Nat.mul_div_cancel_left _ (by decide)

theorem base_case_odd (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
  a (2 * (p - 1) + 1) % p = 1 % p := by
  rw [a_succ (2 * (p - 1))]
  have h_choose : Nat.choose (2 * (p - 1) + 1) 2 = (2 * (p - 1) + 1) * (p - 1) := choose_two_p_minus_one_succ p
  rw [h_choose]
  have h_add : (2 ^ ((2 * (p - 1) + 1) * (p - 1)) + (2 ^ (2 * (p - 1)) - 1) * a (2 * (p - 1))) % p =
    (2 ^ ((2 * (p - 1) + 1) * (p - 1)) % p + ((2 ^ (2 * (p - 1)) - 1) * a (2 * (p - 1))) % p) % p := Nat.add_mod _ _ p
  rw [h_add]
  have h_fermat : 2 ^ (p - 1) % p = 1 % p := Nat.ModEq.pow_card_sub_one_eq_one hp (coprime_two_of_prime_of_ne_two hp hp2)
  have h_term1 : 2 ^ ((2 * (p - 1) + 1) * (p - 1)) % p = 1 % p := by
    have h_pow : 2 ^ ((2 * (p - 1) + 1) * (p - 1)) = (2 ^ (p - 1)) ^ (2 * (p - 1) + 1) := by
      rw [mul_comm, pow_mul]
    rw [h_pow, Nat.pow_mod, h_fermat, ← Nat.pow_mod, one_pow]
  have h_term2 : ((2 ^ (2 * (p - 1)) - 1) * a (2 * (p - 1))) % p = 0 := by
    have h_mul : ((2 ^ (2 * (p - 1)) - 1) * a (2 * (p - 1))) % p = (((2 ^ (2 * (p - 1)) - 1) % p) * (a (2 * (p - 1)) % p)) % p := Nat.mul_mod _ _ p
    rw [h_mul]
    have h_pow2 : (2 ^ (2 * (p - 1))) % p = 1 % p := pow_two_p_minus_one_mod hp hp2
    have h_sub : (2 ^ (2 * (p - 1)) - 1) % p = 0 := Nat.sub_mod_eq_zero_of_mod_eq h_pow2
    rw [h_sub, zero_mul, zero_mod]
  rw [h_term1, h_term2, add_zero, Nat.mod_mod]

theorem choose_shift_formula {p : ℕ} (hp : p.Prime) (d : ℕ) :
  Nat.choose (d + 2 + 2 * (p - 1)) 2 = Nat.choose (d + 2) 2 + (2 * d + 2 * p + 1) * (p - 1) := by
  have hp1 : p - 1 + 1 = p := Nat.sub_add_cancel hp.pos
  generalize h_m : p - 1 = m
  have hp_eq : p = m + 1 := by omega
  rw [hp_eq]
  rw [choose_two_right, choose_two_right]
  have h_sub1 : d + 2 + 2 * m - 1 = d + 1 + 2 * m := by omega
  have h_sub2 : d + 2 - 1 = d + 1 := by omega
  rw [h_sub1, h_sub2]
  have h_sub3 : 2 * d + 2 * (m + 1) + 1 = 2 * d + 2 * m + 3 := by omega
  rw [h_sub3]
  have h_num : (d + 2 + 2 * m) * (d + 1 + 2 * m) = (d + 2) * (d + 1) + ((2 * d + 2 * m + 3) * m) * 2 := by ring
  rw [h_num]
  rw [Nat.add_mul_div_right _ _ (by decide)]

theorem sub_one_mod_eq_of_mod_eq (A B p : ℕ) (h : A % p = B % p) (hA : A ≥ 1) (hB : B ≥ 1) : (A - 1) % p = (B - 1) % p := by
  exact Nat.ModEq.sub hA hB h rfl

theorem a_mod_two_succ (d : ℕ) : a (d + 1) % 2 = 1 := by
  induction d with
  | zero =>
    rfl
  | succ d ih =>
    rw [a_succ (d + 1)]
    have h_choose_pos : Nat.choose (d + 2) 2 ≥ 1 := by
      have h_ge : d + 2 ≥ 2 := by omega
      exact Nat.choose_le_choose 2 h_ge
    have h_pow_choose : 2 ^ Nat.choose (d + 2) 2 % 2 = 0 := by
      have h_pow : 2 ^ Nat.choose (d + 2) 2 = 2 * 2 ^ (Nat.choose (d + 2) 2 - 1) := by
        generalize Nat.choose (d + 2) 2 = K at h_choose_pos ⊢
        have h_eq : K = K - 1 + 1 := by omega
        nth_rw 1 [h_eq]
        rw [pow_add, pow_one, mul_comm]
      rw [h_pow]
      exact Nat.mul_mod_right _ _
    have h_pow_d : 2 ^ (d + 1) = 2 * 2 ^ d := by ring
    have h_pow_d_ge : 2 ^ d ≥ 1 := by
      have : 2 ^ d ≥ 2 ^ 0 := Nat.pow_le_pow_right (by decide) (by omega)
      exact this
    have h_coef : (2 ^ (d + 1) - 1) % 2 = 1 := by
      rw [h_pow_d]
      generalize 2 ^ d = X at h_pow_d_ge ⊢
      omega
    have h_add : (2 ^ Nat.choose (d + 2) 2 + (2 ^ (d + 1) - 1) * a (d + 1)) % 2 =
      (2 ^ Nat.choose (d + 2) 2 % 2 + ((2 ^ (d + 1) - 1) * a (d + 1)) % 2) % 2 := Nat.add_mod _ _ 2
    rw [h_add, h_pow_choose, zero_add]
    have h_mul : ((2 ^ (d + 1) - 1) * a (d + 1)) % 2 = (((2 ^ (d + 1) - 1) % 2) * (a (d + 1) % 2)) % 2 := Nat.mul_mod _ _ 2
    rw [h_mul, h_coef, ih]

theorem a_shift_mod (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (d : ℕ) :
  a (d + 1 + 2 * (p - 1)) % p = a (d + 1) % p := by
  induction d with
  | zero =>
    have h1 : 0 + 1 + 2 * (p - 1) = 2 * (p - 1) + 1 := by omega
    have h2 : 0 + 1 = 1 := by rfl
    rw [h1, h2]
    rw [base_case_odd p hp hp2]
    rfl
  | succ d ih =>
    have h_lhs : d + 1 + 1 + 2 * (p - 1) = (d + 1 + 2 * (p - 1)) + 1 := by omega
    have h_rhs : d + 1 + 1 = (d + 1) + 1 := by omega
    rw [h_lhs, h_rhs]
    rw [a_succ (d + 1 + 2 * (p - 1)), a_succ (d + 1)]
    have h_choose_eq : Nat.choose (d + 1 + 2 * (p - 1) + 1) 2 = Nat.choose (d + 2) 2 + (2 * d + 2 * p + 1) * (p - 1) := by
      have : d + 1 + 2 * (p - 1) + 1 = d + 2 + 2 * (p - 1) := by omega
      rw [this, choose_shift_formula hp d]
    have h_pow_mod_one : 2 ^ ((2 * d + 2 * p + 1) * (p - 1)) % p = 1 % p := by
      have h_pow : 2 ^ ((2 * d + 2 * p + 1) * (p - 1)) = (2 ^ (p - 1)) ^ (2 * d + 2 * p + 1) := by
        rw [mul_comm, pow_mul]
      have h_fermat : 2 ^ (p - 1) % p = 1 % p := Nat.ModEq.pow_card_sub_one_eq_one hp (coprime_two_of_prime_of_ne_two hp hp2)
      rw [h_pow, Nat.pow_mod, h_fermat, ← Nat.pow_mod, one_pow]
    have h_term1_eq : 2 ^ (Nat.choose (d + 2) 2 + (2 * d + 2 * p + 1) * (p - 1)) % p = 2 ^ Nat.choose (d + 2) 2 % p := by
      rw [pow_add]
      have h_mul : (2 ^ Nat.choose (d + 2) 2 * 2 ^ ((2 * d + 2 * p + 1) * (p - 1))) % p =
        ((2 ^ Nat.choose (d + 2) 2 % p) * (2 ^ ((2 * d + 2 * p + 1) * (p - 1)) % p)) % p := Nat.mul_mod _ _ p
      rw [h_mul, h_pow_mod_one]
      rw [← Nat.mul_mod, mul_one]
    have h_pow_eq : 2 ^ (d + 1 + 2 * (p - 1)) % p = 2 ^ (d + 1) % p := by
      rw [pow_add]
      have h_mul : (2 ^ (d + 1) * 2 ^ (2 * (p - 1))) % p =
        ((2 ^ (d + 1) % p) * (2 ^ (2 * (p - 1)) % p)) % p := Nat.mul_mod _ _ p
      rw [h_mul, pow_two_p_minus_one_mod hp hp2]
      rw [← Nat.mul_mod, mul_one]
    have h_coef_eq : (2 ^ (d + 1 + 2 * (p - 1)) - 1) % p = (2 ^ (d + 1) - 1) % p :=
      sub_one_mod_eq_of_mod_eq _ _ p h_pow_eq Nat.one_le_two_pow Nat.one_le_two_pow
    have h_lhs_mod : (2 ^ Nat.choose (d + 1 + 2 * (p - 1) + 1) 2 + (2 ^ (d + 1 + 2 * (p - 1)) - 1) * a (d + 1 + 2 * (p - 1))) % p =
      (2 ^ Nat.choose (d + 1 + 2 * (p - 1) + 1) 2 % p + ((2 ^ (d + 1 + 2 * (p - 1)) - 1) * a (d + 1 + 2 * (p - 1))) % p) % p := Nat.add_mod _ _ p
    rw [h_lhs_mod]
    rw [h_choose_eq, h_term1_eq]
    have h_mul1 : ((2 ^ (d + 1 + 2 * (p - 1)) - 1) * a (d + 1 + 2 * (p - 1))) % p =
      (((2 ^ (d + 1 + 2 * (p - 1)) - 1) % p) * (a (d + 1 + 2 * (p - 1)) % p)) % p := Nat.mul_mod _ _ p
    rw [h_mul1, h_coef_eq, ih]
    have h_mul2 : (((2 ^ (d + 1) - 1) % p) * (a (d + 1) % p)) % p =
      ((2 ^ (d + 1) - 1) * a (d + 1)) % p := (Nat.mul_mod _ _ p).symm
    rw [h_mul2]
    rw [← Nat.add_mod]


theorem oeis_340881_conjecture_0 (p : ℕ) (hp : Nat.Prime p) :
  ∀ (n : ℕ), n ≥ 1 → a (n + 2 * (p - 1)) % p = a n % p := by
  intro n hn
  by_cases hp2 : p = 2
  · subst hp2
    have a_mod_two_any : ∀ (k : ℕ), k ≥ 1 → a k % 2 = 1 := by
      intro k hk
      have h_eq : k = (k - 1) + 1 := by omega
      rw [h_eq]
      exact a_mod_two_succ (k - 1)
    have h1 : n + 2 * (2 - 1) ≥ 1 := by omega
    rw [a_mod_two_any (n + 2 * (2 - 1)) h1, a_mod_two_any n hn]
  · have h_eq : n = (n - 1) + 1 := by omega
    nth_rw 2 [h_eq]
    have h_eq2 : n + 2 * (p - 1) = (n - 1) + 1 + 2 * (p - 1) := by omega
    rw [h_eq2]
    exact a_shift_mod p hp hp2 (n - 1)

#print axioms oeis_340881_conjecture_0
