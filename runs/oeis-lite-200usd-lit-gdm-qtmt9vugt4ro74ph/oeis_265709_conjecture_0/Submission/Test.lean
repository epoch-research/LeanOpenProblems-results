import FormalConjectures.Util.ProblemImports

open Nat Finset ArithmeticFunction

def M : ℕ → ℕ
  | 0 => 0
  | i + 1 => max (M i) (padicValNat 2 (i + 1))

lemma padicValNat_odd (k : ℕ) : padicValNat 2 (2 * k + 1) = 0 := by
  have h_odd : (2 * k + 1) % 2 = 1 := by omega
  exact padicValNat.eq_zero_of_not_dvd (fun h => by
    have : (2 * k + 1) % 2 = 0 := Nat.mod_eq_zero_of_dvd h
    omega)

lemma padicValNat_even (k : ℕ) (hk : k ≠ 0) : padicValNat 2 (2 * k) = padicValNat 2 k + 1 := by
  have h2 : (2 : ℕ) ≠ 0 := by decide
  have h_prime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [mul_comm]
  have h_val := @padicValNat.mul 2 k 2 h_prime hk h2
  rw [h_val]
  have h_two : padicValNat 2 2 = 1 := padicValNat_self
  rw [h_two]

lemma M_one : M 1 = 0 := by
  have : M 1 = max (M 0) (padicValNat 2 1) := rfl
  rw [this]
  have : padicValNat 2 1 = 0 := by
    have : 2 * 0 + 1 = 1 := by ring
    rw [← this, padicValNat_odd]
  rw [this]
  rfl

lemma M_two : M 2 = 1 := by
  have : M 2 = max (M 1) (padicValNat 2 2) := rfl
  rw [this, M_one]
  have : padicValNat 2 2 = 1 := padicValNat_self
  rw [this]
  rfl

lemma M_even (k : ℕ) (hk : k ≥ 1) : M (2 * k) = M k + 1 := by
  induction k, hk using Nat.le_induction with
  | base =>
    rw [mul_one]
    rw [M_two, M_one]
  | succ k hk ih =>
    have h_eq : 2 * (k + 1) = 2 * k + 2 := by ring
    rw [h_eq]
    have h_def1 : M (2 * k + 2) = max (M (2 * k + 1)) (padicValNat 2 (2 * k + 2)) := rfl
    rw [h_def1]
    have h_def2 : M (2 * k + 1) = max (M (2 * k)) (padicValNat 2 (2 * k + 1)) := rfl
    rw [h_def2]
    rw [padicValNat_odd k]
    have h_max_zero : max (M (2 * k)) 0 = M (2 * k) := Nat.max_zero (M (2 * k))
    rw [h_max_zero, ih]
    have h_even_val : padicValNat 2 (2 * k + 2) = padicValNat 2 (k + 1) + 1 := by
      have h_eq2 : 2 * k + 2 = 2 * (k + 1) := by ring
      have h_nz : k + 1 ≠ 0 := by omega
      rw [h_eq2, padicValNat_even (k+1) h_nz]
    rw [h_even_val]
    have h_max_add : max (M k + 1) (padicValNat 2 (k + 1) + 1) = max (M k) (padicValNat 2 (k + 1)) + 1 := by
      omega
    rw [h_max_add]
    rfl

lemma M_ne (i : ℕ) (hi : i ≥ 1) : M i ≠ padicValNat 2 (i + 1) := by
  induction' i using Nat.strong_induction_on with i ih
  by_cases h_one : i = 1
  · subst h_one
    rw [M_one]
    have : padicValNat 2 2 = 1 := padicValNat_self
    rw [this]
    decide
  · have hi_gt : i > 1 := by omega
    by_cases h_even : i % 2 = 0
    · -- i is even
      have ⟨k, hk_eq⟩ : ∃ k, i = 2 * k := ⟨i / 2, by omega⟩
      have hk_ge : k ≥ 1 := by omega
      rw [hk_eq]
      rw [M_even k hk_ge]
      have h_odd_val : padicValNat 2 (2 * k + 1) = 0 := padicValNat_odd k
      rw [h_odd_val]
      omega
    · -- i is odd
      have ⟨k, hk_eq⟩ : ∃ k, i = 2 * k + 1 := ⟨i / 2, by omega⟩
      have hk_ge : k ≥ 1 := by omega
      rw [hk_eq]
      -- M (2*k + 1) = max (M (2*k)) (padicValNat 2 (2*k + 1))
      have h_def : M (2 * k + 1) = max (M (2 * k)) (padicValNat 2 (2 * k + 1)) := rfl
      rw [h_def]
      rw [padicValNat_odd k]
      have h_max_zero : max (M (2 * k)) 0 = M (2 * k) := Nat.max_zero (M (2 * k))
      rw [h_max_zero]
      rw [M_even k hk_ge]
      have h_even_val : padicValNat 2 (2 * k + 2) = padicValNat 2 (k + 1) + 1 := by
        have h_eq : 2 * k + 2 = 2 * (k + 1) := by ring
        have h_nz : k + 1 ≠ 0 := by omega
        rw [h_eq, padicValNat_even (k+1) h_nz]
      have h_step : 2 * k + 1 + 1 = 2 * k + 2 := rfl
      rw [h_step, h_even_val]
      -- we want to use ih k
      have hk_lt : k < i := by omega
      have ih_k := ih k hk_lt hk_ge
      omega

lemma padicValNat_odd_pow (p : ℕ) (hp : p % 2 = 1) (k : ℕ) : (p ^ k) % 2 = 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    rw [Nat.mul_mod]
    rw [ih]
    rw [hp]

lemma p_sq_mod_four (p : ℕ) (hp : p % 2 = 1) : (p * p) % 4 = 1 := by
  have : p % 4 = 1 ∨ p % 4 = 3 := by omega
  rcases this with h | h
  · rw [Nat.mul_mod, h]
  · rw [Nat.mul_mod, h]

lemma p_sq_pow_mod_four (p : ℕ) (hp : p % 2 = 1) (r : ℕ) : ((p * p) ^ r) % 4 = 1 := by
  have h_p2 := p_sq_mod_four p hp
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ, Nat.mul_mod, ih, h_p2]

lemma padicValNat_pow_two_plus_one_all (p : ℕ) (hp : p % 2 = 1) (r : ℕ) : (p ^ (2 * r)) % 4 = 1 := by
  have h_eq : p ^ (2 * r) = (p * p) ^ r := by ring
  rw [h_eq]
  exact p_sq_pow_mod_four p hp r

lemma padicValNat_pow_two_plus_one (p : ℕ) (hp : p % 2 = 1) (m : ℕ) (_ : m ≥ 1) : padicValNat 2 (p ^ (2 * m) + 1) = 1 := by
  have h_pow := padicValNat_pow_two_plus_one_all p hp m
  have h_mod : (p ^ (2 * m) + 1) % 4 = 2 := by
    rw [Nat.add_mod]
    rw [h_pow]
  have h_div : 2 ∣ (p ^ (2 * m) + 1) := by
    have : (p ^ (2 * m) + 1) % 2 = 0 := by
      have : (p ^ (2 * m)) % 2 = 1 := padicValNat_odd_pow p hp (2 * m)
      omega
    exact Nat.dvd_of_mod_eq_zero this
  have h_ndiv : ¬ 4 ∣ (p ^ (2 * m) + 1) := by
    intro h
    have : (p ^ (2 * m) + 1) % 4 = 0 := Nat.mod_eq_zero_of_dvd h
    omega
  have h_nz : p ^ (2 * m) + 1 ≠ 0 := by omega
  have h_prime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : 1 ≤ padicValNat 2 (p ^ (2 * m) + 1) := by
    exact one_le_padicValNat_of_dvd h_nz h_div
  have h2 : padicValNat 2 (p ^ (2 * m) + 1) < 2 := by
    by_contra h_le
    push_neg at h_le
    have h_dvd : 2 ^ 2 ∣ (p ^ (2 * m) + 1) := by
      exact (padicValNat_dvd_iff_le h_nz).mpr h_le
    change 4 ∣ (p ^ (2 * m) + 1) at h_dvd
    exact h_ndiv h_dvd
  omega

lemma nat_sub_mul (A : ℕ) (hA : A ≥ 1) : (A - 1) * (A + 1) = A * A - 1 := by
  rcases Nat.exists_eq_succ_of_ne_zero (by omega : A ≠ 0) with ⟨B, rfl⟩
  have h1 : (B + 1 - 1) * (B + 1 + 1) = B * (B + 2) := rfl
  have h2 : (B + 1) * (B + 1) - 1 = B * (B + 2) := by
    have h_eq : (B + 1) * (B + 1) = B * (B + 2) + 1 := by ring
    rw [h_eq]
    rfl
  rw [h1, h2]

lemma sum_odd_terms (p : ℕ) (hp : p % 2 = 1) (k : ℕ) : (∑ x ∈ range (2 * k + 1), (p ^ 2) ^ x) % 2 = 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h_step1 : (∑ x ∈ range (2 * (k + 1) + 1), (p ^ 2) ^ x) =
                   (∑ x ∈ range (2 * k + 1), (p ^ 2) ^ x) + (p ^ 2) ^ (2 * k + 1) + (p ^ 2) ^ (2 * k + 2) := by
      have h_eq_succ : 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 := by omega
      rw [h_eq_succ, sum_range_succ, sum_range_succ]
    rw [h_step1]
    have hp2 : (p ^ 2) % 2 = 1 := by
      have : p ^ 2 = p * p := by ring
      rw [this, Nat.mul_mod, hp]
    have h_odd1 : (p ^ 2) ^ (2 * k + 1) % 2 = 1 := padicValNat_odd_pow (p ^ 2) hp2 (2 * k + 1)
    have h_odd2 : (p ^ 2) ^ (2 * k + 2) % 2 = 1 := padicValNat_odd_pow (p ^ 2) hp2 (2 * k + 2)
    have h_add_mod_three : ∀ (A B C : ℕ), (A + B + C) % 2 = ((A % 2 + B % 2) % 2 + C % 2) % 2 := by
      intro A B C
      have h_assoc : A + B + C = (A + B) + C := by ring
      rw [h_assoc, Nat.add_mod, Nat.add_mod A B 2]
    rw [h_add_mod_three, ih, h_odd1, h_odd2]

lemma lte_lemma (p : ℕ) (hp : p % 2 = 1) (hp_prime : p.Prime) (n : ℕ) (hn : n ≥ 1) :
  padicValNat 2 (p ^ (2 * n) - 1) = padicValNat 2 (p ^ 2 - 1) + padicValNat 2 n := by
  induction' n using Nat.strong_induction_on with n ih
  have hp3 : p ≥ 3 := by
    have : p ≥ 2 := hp_prime.two_le
    omega
  by_cases h_even : n % 2 = 0
  · -- n is even
    have ⟨k, hk_eq⟩ : ∃ k, n = 2 * k := ⟨n / 2, by omega⟩
    have hk_ge : k ≥ 1 := by omega
    subst hk_eq
    have h_split : p ^ (2 * (2 * k)) - 1 = (p ^ (2 * k) - 1) * (p ^ (2 * k) + 1) := by
      have h_eq : p ^ (2 * (2 * k)) = (p ^ (2 * k)) * (p ^ (2 * k)) := by ring
      have h_ge2 : p ^ (2 * k) ≥ 1 := by
        have : p ^ (2 * k) ≥ p ^ 2 := Nat.pow_le_pow_right (by omega) (by omega)
        have : p ^ 2 ≥ 9 := by nlinarith
        omega
      rw [h_eq]
      exact (nat_sub_mul (p ^ (2 * k)) h_ge2).symm
    have h_nz1 : p ^ (2 * k) - 1 ≠ 0 := by
      have : p ^ (2 * k) ≥ p ^ 2 := Nat.pow_le_pow_right (by omega) (by omega)
      have : p ^ 2 ≥ 9 := by nlinarith
      omega
    have h_nz2 : p ^ (2 * k) + 1 ≠ 0 := by omega
    rw [h_split]
    have h_prime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h_val := @padicValNat.mul 2 (p ^ (2 * k) - 1) (p ^ (2 * k) + 1) h_prime h_nz1 h_nz2
    rw [h_val]
    have ih_k := ih k (by omega) hk_ge
    rw [ih_k]
    have h_even_val : padicValNat 2 (p ^ (2 * k) + 1) = 1 := padicValNat_pow_two_plus_one p hp k hk_ge
    rw [h_even_val]
    have h_even_n : padicValNat 2 (2 * k) = padicValNat 2 k + 1 := padicValNat_even k (by omega)
    rw [h_even_n]
    omega
  · -- n is odd
    have ⟨k, hk_eq⟩ : ∃ k, n = 2 * k + 1 := ⟨n / 2, by omega⟩
    subst hk_eq
    have h_geom : p ^ (2 * (2 * k + 1)) - 1 = (p ^ 2 - 1) * (∑ x ∈ range (2 * k + 1), (p ^ 2) ^ x) := by
      induction' (2 * k + 1) with m ih
      · simp
      · rw [sum_range_succ]
        have h_dist : (p ^ 2 - 1) * (∑ x ∈ range m, (p ^ 2) ^ x + (p ^ 2) ^ m) =
                      (p ^ 2 - 1) * (∑ x ∈ range m, (p ^ 2) ^ x) + (p ^ 2 - 1) * (p ^ 2) ^ m := by
          exact Nat.mul_add (p ^ 2 - 1) (∑ x ∈ range m, (p ^ 2) ^ x) ((p ^ 2) ^ m)
        rw [h_dist]
        have h_symm : (p ^ 2 - 1) * ∑ x ∈ range m, (p ^ 2) ^ x = p ^ (2 * m) - 1 := ih.symm
        rw [h_symm]
        have h_eq_term : (p ^ 2 - 1) * (p ^ 2) ^ m = (p ^ 2) ^ (m + 1) - (p ^ 2) ^ m := by
          rw [mul_comm]
          have h_sub_mul : ((p^2)^m) * (p^2 - 1) = ((p^2)^m) * p^2 - ((p^2)^m) * 1 := Nat.mul_sub_left_distrib ((p^2)^m) (p^2) 1
          rw [h_sub_mul]
          rw [mul_one, ← pow_succ]
        rw [h_eq_term]
        have h_pow_eq : p ^ (2 * (m + 1)) = (p ^ 2) ^ (m + 1) := by ring
        have h_pow_eq_m : p ^ (2 * m) = (p ^ 2) ^ m := by ring
        have h_p2_ge : 1 ≤ p ^ 2 := by
          have : p ^ 2 ≥ 9 := by nlinarith
          omega
        have h_geA : (p ^ 2) ^ (m + 1) ≥ (p ^ 2) ^ m := by
          have h_eq_add : (p ^ 2) ^ (m + 1) = (p ^ 2) ^ m * p ^ 2 := by ring
          rw [h_eq_add]
          have h_le := Nat.mul_le_mul_left ((p ^ 2) ^ m) h_p2_ge
          rw [mul_one] at h_le
          exact h_le
        rw [h_pow_eq, h_pow_eq_m]
        have h_ge1 : (p ^ 2) ^ m ≥ 1 := Nat.one_le_pow m (p ^ 2) h_p2_ge
        omega
    have h_p2_ge9 : p ^ 2 ≥ 9 := by nlinarith
    have h_nz1 : p ^ 2 - 1 ≠ 0 := by omega
    have h_sum_odd : (∑ x ∈ range (2 * k + 1), (p ^ 2) ^ x) % 2 = 1 := sum_odd_terms p hp k
    have h_nz2 : (∑ x ∈ range (2 * k + 1), (p ^ 2) ^ x) ≠ 0 := by omega
    have h_prime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [h_geom]
    have h_val := @padicValNat.mul 2 (p ^ 2 - 1) (∑ x ∈ range (2 * k + 1), (p ^ 2) ^ x) h_prime h_nz1 h_nz2
    rw [h_val]
    have h_val_zero : padicValNat 2 (∑ x ∈ range (2 * k + 1), (p ^ 2) ^ x) = 0 := by
      exact padicValNat.eq_zero_of_not_dvd (fun h => by
        have : (∑ x ∈ range (2 * k + 1), (p ^ 2) ^ x) % 2 = 0 := Nat.mod_eq_zero_of_dvd h
        omega)
    rw [h_val_zero]
    have h_odd_n : padicValNat 2 (2 * k + 1) = 0 := padicValNat_odd k
    rw [h_odd_n]

lemma geom_sum_nat (p : ℕ) (hp : p ≥ 1) (k : ℕ) : p ^ k - 1 = (p - 1) * (∑ x ∈ range k, p ^ x) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, mul_add, ← ih]
    have : (p - 1) * p ^ k = p ^ (k + 1) - p ^ k := by
      rw [mul_comm, Nat.mul_sub_left_distrib, mul_one, ← pow_succ]
    rw [this]
    have : p ^ (k + 1) ≥ p ^ k := Nat.pow_le_pow_right hp (by omega)
    have : p ^ k ≥ 1 := Nat.one_le_pow k p hp
    omega

lemma sigma_one_pow_prime (p : ℕ) [hp : Fact p.Prime] (j : ℕ) :
  (sigma 1) (p^j) = ∑ x ∈ range (j + 1), p ^ x := by
  rw [ArithmeticFunction.sigma_one_apply]
  rw [Nat.divisors_prime_pow hp.elim j]
  rw [Finset.sum_map]
  rfl

lemma sum_odd_terms_p (p : ℕ) (hp : p % 2 = 1) (k : ℕ) : (∑ x ∈ range (2 * k + 1), p ^ x) % 2 = 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h_step1 : (∑ x ∈ range (2 * (k + 1) + 1), p ^ x) =
                   (∑ x ∈ range (2 * k + 1), p ^ x) + p ^ (2 * k + 1) + p ^ (2 * k + 2) := by
      have h_eq_succ : 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 := by omega
      rw [h_eq_succ, sum_range_succ, sum_range_succ]
    rw [h_step1]
    have h_odd1 : p ^ (2 * k + 1) % 2 = 1 := padicValNat_odd_pow p hp (2 * k + 1)
    have h_odd2 : p ^ (2 * k + 2) % 2 = 1 := padicValNat_odd_pow p hp (2 * k + 2)
    have h_add_mod_three : ∀ (A B C : ℕ), (A + B + C) % 2 = ((A % 2 + B % 2) % 2 + C % 2) % 2 := by
      intro A B C
      have h_assoc : A + B + C = (A + B) + C := by ring
      rw [h_assoc, Nat.add_mod, Nat.add_mod A B 2]
    rw [h_add_mod_three, ih, h_odd1, h_odd2]

lemma padicValNat_sigma_even (p : ℕ) (hp : p % 2 = 1) [Fact p.Prime] (i : ℕ) :
  padicValNat 2 (sigma 1 (p ^ (2 * i))) = 0 := by
  rw [sigma_one_pow_prime p (2 * i)]
  exact padicValNat.eq_zero_of_not_dvd (fun h => by
    have : (∑ x ∈ range (2 * i + 1), p ^ x) % 2 = 0 := Nat.mod_eq_zero_of_dvd h
    have h_odd := sum_odd_terms_p p hp i
    omega)

lemma padicValNat_sigma_odd (p : ℕ) (hp : p % 2 = 1) (hp_prime : p.Prime) (i : ℕ) :
  padicValNat 2 (sigma 1 (p ^ (2 * i + 1))) = padicValNat 2 (p + 1) + padicValNat 2 (i + 1) := by
  have h_fact : Fact p.Prime := ⟨hp_prime⟩
  rw [sigma_one_pow_prime p (2 * i + 1)]
  have h_geom := geom_sum_nat p (by omega : p ≥ 1) (2 * (i + 1))
  have h_eq_sum : (∑ x ∈ range (2 * i + 2), p ^ x) = ∑ x ∈ range (2 * (i + 1)), p ^ x := by
    congr 2; ring
  rw [h_eq_sum]
  have h_geom_eq : p ^ (2 * (i + 1)) - 1 = (p - 1) * (∑ x ∈ range (2 * (i + 1)), p ^ x) := h_geom
  have h_nz1 : p - 1 ≠ 0 := by omega
  have h_nz2 : (∑ x ∈ range (2 * (i + 1)), p ^ x) ≠ 0 := by
    have h_eq_range : 2 * (i + 1) = 2 * i + 1 + 1 := by ring
    have h_ge1 : (∑ x ∈ range (2 * (i + 1)), p ^ x) ≥ 1 := by
      rw [h_eq_range, sum_range_succ']
      simp
    omega
  have h_prime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h_val := @padicValNat.mul 2 (p - 1) (∑ x ∈ range (2 * (i + 1)), p ^ x) h_prime h_nz1 h_nz2
  have h_lte := lte_lemma p hp hp_prime (i + 1) (by omega)
  rw [← h_geom_eq] at h_val
  rw [h_lte] at h_val
  have h_split_p2 : p ^ 2 - 1 = (p - 1) * (p + 1) := by
    have : p ^ 2 = p * p := by ring
    rw [this]
    exact (nat_sub_mul p (by omega : p ≥ 1)).symm
  have h_nz_p1 : p - 1 ≠ 0 := by omega
  have h_nz_p2 : p + 1 ≠ 0 := by omega
  have h_val_p2 := @padicValNat.mul 2 (p - 1) (p + 1) h_prime h_nz_p1 h_nz_p2
  rw [h_split_p2, h_val_p2] at h_val
  omega

lemma rat_num_den_mul (q : ℚ) : (q.num : ℚ) = q * (q.den : ℚ) := by
  have h := Rat.num_div_den q
  have h_den : ((q.den : ℕ) : ℚ) ≠ 0 := by
    have : q.den > 0 := q.den_pos
    exact_mod_cast _root_.ne_of_gt this
  have h_mul := congr_arg (fun x => x * (q.den : ℚ)) h
  dsimp only at h_mul
  rw [div_mul_cancel₀ _ h_den] at h_mul
  exact h_mul

lemma rat_mul_num_eq (q1 q2 : ℚ) (h : (q1 * q2).den = 1) :
  (q1.num * q2.num : ℚ) = ((q1 * q2).num : ℚ) * (q1.den : ℚ) * (q2.den : ℚ) := by
  have h1 := rat_num_den_mul q1
  have h2 := rat_num_den_mul q2
  have h12 : (q1 * q2 : ℚ) = ((q1 * q2).num : ℚ) := by
    have h_eq := Rat.num_div_den (q1 * q2)
    rw [h] at h_eq
    simp at h_eq
    exact h_eq.symm
  rw [h1, h2, ← h12]
  ring

lemma rat_mul_num_eq_int (q1 q2 : ℚ) (h : (q1 * q2).den = 1) :
  q1.num * q2.num = (q1 * q2).num * (q1.den : ℤ) * (q2.den : ℤ) := by
  have h_eq := rat_mul_num_eq q1 q2 h
  have h_cast : ((q1.num * q2.num : ℤ) : ℚ) = (((q1 * q2).num * (q1.den : ℤ) * (q2.den : ℤ) : ℤ) : ℚ) := by
    push_cast
    exact h_eq
  exact_mod_cast h_cast

lemma rat_mul_int_dvd (q1 q2 : ℚ) (h : (q1 * q2).den = 1) : (q2.den : ℤ) ∣ q1.num := by
  have h_eq := rat_mul_num_eq_int q1 q2 h
  have h_dvd : (q2.den : ℤ) ∣ q1.num * q2.num := by
    rw [h_eq]
    use (q1 * q2).num * (q1.den : ℤ)
    ring
  have h_cop : Int.gcd q2.num q2.den = 1 := q2.reduced
  have h_gcd_comm : Int.gcd q2.den q2.num = 1 := by
    rw [Int.gcd_comm]
    exact h_cop
  exact Int.dvd_of_dvd_mul_left_of_gcd_one h_dvd h_gcd_comm

lemma rat_mul_int_dvd_left (q1 q2 : ℚ) (h : (q1 * q2).den = 1) : (q1.den : ℤ) ∣ q2.num := by
  rw [mul_comm] at h
  exact rat_mul_int_dvd q2 q1 h

lemma coprime_den (q1 q2 : ℚ) (hq1 : q1.num > 0) (h : (q1 * q2).den = 1) : Nat.Coprime q1.den q2.den := by
  have hd21 : (q2.den : ℤ) ∣ q1.num := rat_mul_int_dvd q1 q2 h
  have h_eq : q1.num = (q1.num.natAbs : ℤ) := (Int.natAbs_of_nonneg (le_of_lt hq1)).symm
  rw [h_eq] at hd21
  have hd21_nat : q2.den ∣ q1.num.natAbs := by
    exact_mod_cast hd21
  have h_gcd : Nat.gcd q1.den q2.den ∣ Nat.gcd q1.num.natAbs q1.den := by
    apply Nat.dvd_gcd
    · have h_dvd : Nat.gcd q1.den q2.den ∣ q2.den := Nat.gcd_dvd_right q1.den q2.den
      exact dvd_trans h_dvd hd21_nat
    · exact Nat.gcd_dvd_left q1.den q2.den
  have h_cop : Nat.gcd q1.num.natAbs q1.den = 1 := q1.reduced
  rw [h_cop] at h_gcd
  exact Nat.eq_one_of_dvd_one h_gcd

lemma coprime_den_symm (q1 q2 : ℚ) (hq2 : q2.num > 0) (h : (q1 * q2).den = 1) : Nat.Coprime q2.den q1.den := by
  have h_mul : (q2 * q1).den = 1 := by
    rw [mul_comm] at h
    exact h
  exact coprime_den q2 q1 hq2 h_mul

lemma rat_mul_eq_mul (q1 q2 : ℚ) (hq1 : q1.num > 0) (hq2 : q2.num > 0) (h : (q1 * q2).den = 1) :
  q1 * q2 = ( ((q1.num.natAbs / q2.den) * (q2.num.natAbs / q1.den) : ℕ) : ℚ) := by
  have hd21 : q2.den ∣ q1.num.natAbs := by
    have h_dvd : (q2.den : ℤ) ∣ q1.num := rat_mul_int_dvd q1 q2 h
    have h_eq : q1.num = (q1.num.natAbs : ℤ) := (Int.natAbs_of_nonneg (le_of_lt hq1)).symm
    rw [h_eq] at h_dvd
    exact_mod_cast h_dvd
  have hd12 : q1.den ∣ q2.num.natAbs := by
    have h_dvd : (q1.den : ℤ) ∣ q2.num := rat_mul_int_dvd_left q1 q2 h
    have h_eq : q2.num = (q2.num.natAbs : ℤ) := (Int.natAbs_of_nonneg (le_of_lt hq2)).symm
    rw [h_eq] at h_dvd
    exact_mod_cast h_dvd
  have h_eq1 : (q1.num.natAbs : ℚ) = (q1.num.natAbs / q2.den : ℚ) * (q2.den : ℚ) := by
    have h_cancel : q1.num.natAbs = (q1.num.natAbs / q2.den) * q2.den := (Nat.div_mul_cancel hd21).symm
    have h_cast : (q1.num.natAbs : ℚ) = (((q1.num.natAbs / q2.den) * q2.den : ℕ) : ℚ) := by
      exact_mod_cast h_cancel
    push_cast at h_cast
    exact h_cast
  have h_eq2 : (q2.num.natAbs : ℚ) = (q2.num.natAbs / q1.den : ℚ) * (q1.den : ℚ) := by
    have h_cancel : q2.num.natAbs = (q2.num.natAbs / q1.den) * q1.den := (Nat.div_mul_cancel hd12).symm
    have h_cast : (q2.num.natAbs : ℚ) = (((q2.num.natAbs / q1.den) * q1.den : ℕ) : ℚ) := by
      exact_mod_cast h_cancel
    push_cast at h_cast
    exact h_cast
  have h_q1 : q1 = ((q1.num.natAbs / q2.den : ℕ) : ℚ) * (q2.den : ℚ) / (q1.den : ℚ) := by
    have h_q1_def : q1 = (q1.num : ℚ) / (q1.den : ℚ) := (Rat.num_div_den q1).symm
    have h_cast : (q1.num : ℚ) = (q1.num.natAbs : ℚ) := by
      have : q1.num = (q1.num.natAbs : ℤ) := (Int.natAbs_of_nonneg (le_of_lt hq1)).symm
      exact_mod_cast this
    rw [h_q1_def, h_cast, h_eq1]
  have h_q2 : q2 = ((q2.num.natAbs / q1.den : ℕ) : ℚ) * (q1.den : ℚ) / (q2.den : ℚ) := by
    have h_q2_def : q2 = (q2.num : ℚ) / (q2.den : ℚ) := (Rat.num_div_den q2).symm
    have h_cast : (q2.num : ℚ) = (q2.num.natAbs : ℚ) := by
      have : q2.num = (q2.num.natAbs : ℤ) := (Int.natAbs_of_nonneg (le_of_lt hq2)).symm
      exact_mod_cast this
    rw [h_q2_def, h_cast, h_eq2]
  have h_den1 : (q1.den : ℚ) ≠ 0 := by
    have : q1.den > 0 := q1.den_pos
    exact_mod_cast _root_.ne_of_gt this
  have h_den2 : (q2.den : ℚ) ≠ 0 := by
    have : q2.den > 0 := q2.den_pos
    exact_mod_cast _root_.ne_of_gt this
  rw [h_q1, h_q2]
  push_cast
  field_simp
  ring


