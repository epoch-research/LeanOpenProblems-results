import FormalConjectures.Util.ProblemImports

open Nat Finset

theorem sigma1_eq_sigma (m : ℕ) : m.divisors.sum id = ArithmeticFunction.sigma 1 m := by
  rw [ArithmeticFunction.sigma_one_apply]
  rfl

theorem eq_pow_two_of_primeFactors_subset (k : ℕ) (hk : k ≥ 1) (h_sub : ∀ p ∈ k.primeFactors, p = 2) : k.isPowerOfTwo := by
  induction' k using Nat.strong_induction_on with k ih
  rcases k with _ | k
  · -- k = 0
    omega
  · rcases k with _ | k
    · -- k = 1
      use 0
    · -- k ≥ 2
      have hk2 : k + 2 ≥ 2 := by omega
      have hp : (k + 2).minFac.Prime := Nat.minFac_prime (by omega)
      have h_dvd : (k + 2).minFac ∣ k + 2 := Nat.minFac_dvd (k + 2)
      have h_mem : (k + 2).minFac ∈ (k + 2).primeFactors := by
        rw [Nat.mem_primeFactors]
        exact ⟨hp, h_dvd, by omega⟩
      have hp2 : (k + 2).minFac = 2 := h_sub (k + 2).minFac h_mem
      have h_div : 2 ∣ k + 2 := by
        have h_temp := h_dvd
        rw [hp2] at h_temp
        exact h_temp
      rcases h_div with ⟨m, hm⟩
      -- k + 2 = 2 * m
      have hm_lt : m < k + 2 := by omega
      have hm_pos : m ≥ 1 := by omega
      have h_sub_m : ∀ p ∈ m.primeFactors, p = 2 := by
        intro p hp_m
        rw [Nat.mem_primeFactors] at hp_m
        have h_dvd_k : p ∣ k + 2 := by
          rw [hm]
          exact dvd_mul_of_dvd_right hp_m.2.1 2
        have h_mem_k : p ∈ (k + 2).primeFactors := by
          rw [Nat.mem_primeFactors]
          exact ⟨hp_m.1, h_dvd_k, by omega⟩
        exact h_sub p h_mem_k
      have ih_m := ih m hm_lt hm_pos h_sub_m
      rcases ih_m with ⟨j, rfl⟩
      use j + 1
      rw [pow_succ]
      omega


theorem exists_prime_factor_ge_three (k : ℕ) (hk : ¬ k.isPowerOfTwo) (hk2 : 2 ≤ k) : ∃ p, p.Prime ∧ p ∣ k ∧ 3 ≤ p := by
  by_contra h_all
  push_neg at h_all
  have h_sub : ∀ p ∈ k.primeFactors, p = 2 := by
    intro p hp_mem
    rw [Nat.mem_primeFactors] at hp_mem
    have hp_le := h_all p hp_mem.1 hp_mem.2.1
    have hp_prime := hp_mem.1
    have h_two := hp_prime.two_le
    omega
  have h_pow := eq_pow_two_of_primeFactors_subset k (by omega) h_sub
  contradiction

theorem divisors_sum_le_two_mul_sub_two (k : ℕ) (hk : ¬ k.isPowerOfTwo) (h_def : k.divisors.sum id < 2 * k) (hk2 : 2 ≤ k) : k.divisors.sum id ≤ 2 * k - 2 := by
  have h_or : k.divisors.sum id ≤ 2 * k - 2 ∨ k.divisors.sum id = 2 * k - 1 := by omega
  rcases h_or with h1 | h2
  · exact h1
  · rcases exists_prime_factor_ge_three k hk hk2 with ⟨p, hp, hp_dvd, hp3⟩
    by_cases hp_k : p = k
    · subst hp_k
      rw [sigma1_eq_sigma] at h2
      have hp_prime : Nat.Prime p := hp
      have h_sum := hp_prime.sum_divisors (f := id)
      simp only [id_eq] at h_sum
      rw [ArithmeticFunction.sigma_one_apply] at h2
      rw [h_sum] at h2
      omega
    · -- p ≠ k
      have hd_dvd : k / p ∣ k := Nat.div_dvd_of_dvd hp_dvd
      have hp_pos : p > 0 := hp.pos
      have hk_pos : k > 0 := by omega
      have h_k_eq : k = p * (k / p) := (Nat.mul_div_cancel' hp_dvd).symm
      have hd_pos : k / p > 0 := Nat.pos_of_ne_zero (by
        intro hc
        rw [hc, mul_zero] at h_k_eq
        omega)
      have hd_ne_one : k / p ≠ 1 := by
        intro hc
        rw [hc, mul_one] at h_k_eq
        exact hp_k h_k_eq.symm
      have hd_ne_k : k / p ≠ k := by
        intro hc
        rw [hc] at h_k_eq
        have hp1 : p = 1 := by
          by_contra hc2
          have : p = 0 ∨ p ≥ 2 := by omega
          rcases this with rfl | hp_ge
          · omega
          · have : p * k > k := by nlinarith
            omega
        have := hp.one_lt
        omega
      by_cases hp_d : p = k / p
      · -- p = k / p, so k = p^2
        have h_k_eq2 : k = p ^ 2 := by
          rw [h_k_eq, ← hp_d]
          ring
        rw [sigma1_eq_sigma] at h2
        have h_sum := Nat.sum_divisors_prime_pow (k := 2) hp (f := id)
        simp only [id_eq] at h_sum
        rw [ArithmeticFunction.sigma_one_apply] at h2
        rw [h_k_eq2] at h2
        rw [h_sum] at h2
        -- sum on range 3 of id (p^x) is 1 + p + p^2
        have h_sum3 : (∑ x ∈ range 3, p ^ x) = 1 + p + p ^ 2 := by
          have h3 : range 3 = insert 2 (insert 1 {0}) := by decide
          rw [h3]
          rw [sum_insert (by decide)]
          rw [sum_insert (by decide)]
          rw [sum_singleton]
          ring
        rw [h_sum3] at h2
        have h_pow_eq : p ^ 2 = p * p := by ring
        rw [h_pow_eq] at h2
        have hp_sub1 : 2 ≤ p - 1 := by omega
        have hp_mul : p * (p - 1) ≥ 6 := by
          have := Nat.mul_le_mul hp3 hp_sub1
          omega
        have hp_sq_sub : p * p - p = p * (p - 1) := by
          rw [Nat.mul_sub_left_distrib, mul_one]
        have hp_sq_ge : p * p ≥ p + 6 := by
          omega
        omega
      · sorry

theorem test_submult (a b : ℕ) (d : ℕ) (hd : d ∣ a * b) : ∃ d1 d2, d1 ∣ a ∧ d2 ∣ b ∧ d = d1 * d2 := by
  exact exists_dvd_and_dvd_of_dvd_mul hd


theorem divisors_mul_subset (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (a * b).divisors ⊆ (a.divisors ×ˢ b.divisors).image (fun p => p.1 * p.2) := by
  intro d hd
  rw [mem_divisors] at hd
  obtain ⟨d1, d2, hd1, hd2, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul hd.1
  rw [mem_image]
  use (d1, d2)
  constructor
  · rw [mem_product, mem_divisors, mem_divisors]
    exact ⟨⟨hd1, ha⟩, hd2, hb⟩
  · rfl


theorem sum_image_le {α β : Type*} [DecidableEq α] [DecidableEq β] (s : Finset α) (f : β → ℕ) (g : α → β) :
    (s.image g).sum (fun y => f y) ≤ s.sum (fun x => f (g x)) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    rw [sum_insert hx]
    by_cases h_mem : g x ∈ s.image g
    · have h_eq : (insert x s).image g = s.image g := by
        ext y
        constructor
        · intro hy
          rw [mem_image] at hy
          rcases hy with ⟨a, ha, rfl⟩
          rw [mem_insert] at ha
          rcases ha with rfl | ha
          · exact h_mem
          · rw [mem_image]
            exact ⟨a, ha, rfl⟩
        · intro hy
          rw [mem_image] at hy
          rcases hy with ⟨a, ha, rfl⟩
          rw [mem_image]
          use a
          rw [mem_insert]
          exact ⟨Or.inr ha, rfl⟩
      rw [h_eq]
      omega
    · have h_eq : (insert x s).image g = insert (g x) (s.image g) := image_insert g x s
      rw [h_eq, sum_insert h_mem]
      omega


theorem divisors_sum_mul_le (a b : ℕ) :
    (a * b).divisors.sum id ≤ a.divisors.sum id * b.divisors.sum id := by
  by_cases ha : a = 0
  · subst ha
    simp
  · by_cases hb : b = 0
    · subst hb
      simp
    · have h_sub := divisors_mul_subset a b ha hb
      have h_le : (a * b).divisors.sum id ≤ ((a.divisors ×ˢ b.divisors).image (fun p => p.1 * p.2)).sum id := sum_le_sum_of_subset h_sub
      have h_img := sum_image_le (a.divisors ×ˢ b.divisors) id (fun p => p.1 * p.2)
      simp only [id_eq] at h_img ⊢
      have h_trans : (a * b).divisors.sum id ≤ (a.divisors ×ˢ b.divisors).sum (fun p => p.1 * p.2) := le_trans h_le h_img
      rw [sum_product] at h_trans
      have h_eq : (∑ x ∈ a.divisors, ∑ y ∈ b.divisors, x * y) = a.divisors.sum id * b.divisors.sum id := by
        rw [← sum_mul_sum]
        rfl
      rw [h_eq] at h_trans
      exact h_trans


theorem ord_two_and_odd (k : ℕ) (hk : k ≠ 0) : ∃ a m, k = 2^a * m ∧ m % 2 = 1 := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases h_even : 2 ∣ k
    · rcases h_even with ⟨m, rfl⟩
      have hm_pos : m ≠ 0 := by omega
      have hm_lt : m < 2 * m := by omega
      rcases ih m hm_lt hm_pos with ⟨a, m', rfl, h_odd⟩
      use a + 1, m'
      constructor
      · ring
      · exact h_odd
    · use 0, k
      constructor
      · simp
      · rcases Nat.mod_two_eq_zero_or_one k with h_zero | h_one
        · have : 2 ∣ k := dvd_of_mod_eq_zero h_zero
          contradiction
        · exact h_one

theorem coprime_pow_two_odd (a m : ℕ) (hm : m % 2 = 1) : Nat.Coprime (2 ^ a) m := by
  apply Nat.Coprime.pow_left
  rw [Nat.coprime_iff_gcd_eq_one]
  have h_dvd : Nat.gcd 2 m ∣ 2 := Nat.gcd_dvd_left 2 m
  have : Nat.gcd 2 m = 1 ∨ Nat.gcd 2 m = 2 := by
    have h_pos : Nat.gcd 2 m > 0 := Nat.gcd_pos_of_pos_left m (by decide)
    have h_le : Nat.gcd 2 m ≤ 2 := Nat.le_of_dvd (by decide) h_dvd
    omega
  rcases this with h1 | h2
  · exact h1
  · have hd := Nat.gcd_dvd_right 2 m
    rw [h2] at hd
    have h_mod : m % 2 = 0 := Nat.mod_eq_zero_of_dvd hd
    omega

