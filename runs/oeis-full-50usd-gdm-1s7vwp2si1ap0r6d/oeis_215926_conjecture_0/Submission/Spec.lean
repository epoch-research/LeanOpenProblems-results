import FormalConjectures.Util.ProblemImports

open Nat Finset

noncomputable def a (n : ℕ) : ℕ :=
  let sigma1 (m : ℕ) : ℕ := m.divisors.sum id
  sInf {k : ℕ | sigma1 k < 2 * k ∧ 2 * (k * n) ≤ sigma1 (k * n)}

def S (n : ℕ) : Set ℕ :=
  {k : ℕ | k.divisors.sum id < 2 * k ∧ 2 * (k * n) ≤ (k * n).divisors.sum id}

theorem a_eq_S (n : ℕ) : a n = sInf (S n) := rfl

theorem sigma1_eq_sigma (m : ℕ) : m.divisors.sum id = ArithmeticFunction.sigma 1 m := by
  rw [ArithmeticFunction.sigma_one_apply]
  rfl

theorem coprime_three_pow_two (k : ℕ) : Coprime 3 (2 ^ k) := by
  apply Coprime.pow_right
  decide

theorem divisors_sum_two_pow_ge (k : ℕ) (hk : k ≥ 1) : 2 ^ k + 2 ^ (k - 1) ≤ (2 ^ k).divisors.sum id := by
  have h_pos : 2 ^ k > 0 := pow_pos (by decide) k
  have h_pos2 : 2 ^ (k - 1) > 0 := pow_pos (by decide) (k - 1)
  have h_eq : 2 ^ k = 2 ^ (k - 1) * 2 := by
    rw [← pow_succ, Nat.sub_add_cancel hk]
  have h1 : 2 ^ k ∈ (2 ^ k).divisors := by
    rw [mem_divisors]
    exact ⟨dvd_rfl, Nat.ne_of_gt h_pos⟩
  have h2 : 2 ^ (k - 1) ∈ (2 ^ k).divisors := by
    rw [mem_divisors]
    constructor
    · -- 2^(k-1) | 2^k
      rw [h_eq]
      exact dvd_mul_right (2 ^ (k - 1)) 2
    · -- 2^k ≠ 0
      exact Nat.ne_of_gt h_pos
  have hne : 2 ^ k ∉ ({2 ^ (k - 1)} : Finset ℕ) := by
    simp only [mem_singleton]
    have h_lt : 2 ^ (k - 1) < 2 ^ k := by
      rw [h_eq]
      linarith [h_pos2]
    exact h_lt.ne'
  have h_subset : {2 ^ k, 2 ^ (k - 1)} ⊆ (2 ^ k).divisors := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact h1
    · exact h2
  have h_pair : ({2 ^ k, 2 ^ (k - 1)} : Finset ℕ).sum id = 2 ^ k + 2 ^ (k - 1) := by
    rw [sum_insert hne, sum_singleton, id_eq, id_eq]
  rw [← h_pair]
  apply sum_le_sum_of_subset h_subset

theorem mem_S_three_of_two_pow (k : ℕ) (hk : k ≥ 1) : 3 ∈ S (2 ^ k) := by
  have h_sum3 : (3 : ℕ).divisors.sum id = 4 := by decide
  unfold S
  simp only [Set.mem_setOf_eq]
  constructor
  · -- 3.divisors.sum id < 2 * 3
    rw [h_sum3]
    decide
  · -- 2 * (3 * 2^k) ≤ (3 * 2^k).divisors.sum id
    have h_mult : (3 * 2 ^ k).divisors.sum id = (3 : ℕ).divisors.sum id * (2 ^ k).divisors.sum id := by
      rw [sigma1_eq_sigma, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (coprime_three_pow_two k), ← sigma1_eq_sigma, ← sigma1_eq_sigma]
    rw [h_mult, h_sum3]
    have h_le := divisors_sum_two_pow_ge k hk
    have h_calc : 2 * (3 * 2 ^ k) = 4 * (2 ^ k + 2 ^ (k - 1)) := by
      have h_eq2 : 2 ^ k = 2 ^ (k - 1) * 2 := by
        rw [← pow_succ, Nat.sub_add_cancel hk]
      rw [h_eq2]
      ring
    rw [h_calc]
    gcongr

theorem divisors_sum_two_pow_lt (k : ℕ) : (2 ^ k).divisors.sum id < 2 ^ (k + 1) := by
  have h_prime : Nat.Prime 2 := Nat.prime_two
  have h_sigma : (2 ^ k).divisors.sum id = ∑ j ∈ range (k + 1), 2 ^ j := by
    rw [sigma1_eq_sigma]
    have h_pow := ArithmeticFunction.sigma_apply_prime_pow (k := 1) (i := k) h_prime
    simp only [mul_one] at h_pow
    exact h_pow
  rw [h_sigma]
  have h_geom := geomSum_eq (m := 2) (by decide) (k + 1)
  rw [h_geom]
  have h_div : (2 ^ (k + 1) - 1) / (2 - 1) = 2 ^ (k + 1) - 1 := by rw [Nat.div_one]
  rw [h_div]
  exact Nat.sub_lt (by positivity) (by decide)

theorem zero_not_mem_S (n : ℕ) : 0 ∉ S n := by
  intro h
  unfold S at h
  simp at h

theorem sInf_eq_three_of_mem (s : Set ℕ) (h3 : 3 ∈ s) (h0 : 0 ∉ s) (h1 : 1 ∉ s) (h2 : 2 ∉ s) : sInf s = 3 := by
  have h_ne : s.Nonempty := ⟨3, h3⟩
  have h_le : ∀ x ∈ s, 3 ≤ x := by
    intro x hx
    cases x with
    | zero => contradiction
    | succ x =>
      cases x with
      | zero =>
        have : 1 ∈ s := hx
        contradiction
      | succ x =>
        cases x with
        | zero =>
          have : 2 ∈ s := hx
          contradiction
        | succ x =>
          omega
  exact le_antisymm (Nat.sInf_le h3) (le_csInf h_ne h_le)

theorem a_eq_three_of_power_of_two (k : ℕ) (hk : k ≥ 1) : a (2 ^ k) = 3 := by
  rw [a_eq_S]
  apply sInf_eq_three_of_mem (S (2 ^ k))
  · exact mem_S_three_of_two_pow k hk
  · exact zero_not_mem_S (2 ^ k)
  · -- 1 ∉ S (2^k)
    unfold S
    simp only [Set.mem_setOf_eq, divisors_one, sum_singleton, id_eq, one_mul]
    intro hc
    have h_lt := divisors_sum_two_pow_lt k
    have h_sum_id : (2 ^ k).divisors.sum id = ∑ x ∈ (2 ^ k).divisors, x := rfl
    rw [h_sum_id] at h_lt
    have h_eq_pow : 2 * 2 ^ k = 2 ^ (k + 1) := by ring
    rw [h_eq_pow] at hc
    linarith [hc.2]
  · -- 2 ∉ S (2^k)
    unfold S
    simp only [Set.mem_setOf_eq]
    intro hc
    have h_lt := divisors_sum_two_pow_lt (k + 1)
    have h_sum_id : (2 ^ (k + 1)).divisors.sum id = ∑ x ∈ (2 ^ (k + 1)).divisors, x := rfl
    rw [h_sum_id] at h_lt
    have h_eq3 : 2 * 2 ^ k = 2 ^ (k + 1) := by ring
    rw [h_eq3] at hc
    have h_eq4 : 2 * 2 ^ (k + 1) = 2 ^ (k + 2) := by ring
    rw [h_eq4] at hc
    -- also k+1+1 in h_lt is k+2
    have h_eq5 : k + 1 + 1 = k + 2 := by omega
    rw [h_eq5] at h_lt
    linarith [hc.2]

theorem sInf_eq_one_of_mem_one (s : Set ℕ) (h1 : 1 ∈ s) (h0 : 0 ∉ s) : sInf s = 1 := by
  have h_ne : s.Nonempty := ⟨1, h1⟩
  have h_le : ∀ x ∈ s, 1 ≤ x := by
    intro x hx
    cases x with
    | zero => contradiction
    | succ x' => exact Nat.le_add_left 1 x'
  exact le_antisymm (Nat.sInf_le h1) (le_csInf h_ne h_le)

theorem mem_S_one_of_non_deficient (n : ℕ) (h : 2 * n ≤ n.divisors.sum id) : 1 ∈ S n := by
  unfold S
  simp at h ⊢
  exact h

theorem a_eq_one_of_non_deficient (n : ℕ) (h : 2 * n ≤ n.divisors.sum id) : a n = 1 := by
  rw [a_eq_S]
  exact sInf_eq_one_of_mem_one (S n) (mem_S_one_of_non_deficient n h) (zero_not_mem_S n)

theorem test_coprime_2 (n : ℕ) (hn : n % 2 = 1) : Nat.Coprime 2 n := by
  rw [Nat.coprime_iff_gcd_eq_one]
  have h_dvd : Nat.gcd 2 n ∣ 2 := Nat.gcd_dvd_left 2 n
  have h_cases : Nat.gcd 2 n = 1 ∨ Nat.gcd 2 n = 2 := by
    have h_pos : Nat.gcd 2 n > 0 := Nat.gcd_pos_of_pos_left n (by decide)
    rcases h_dvd with ⟨c, hc⟩
    -- 2 = Nat.gcd 2 n * c
    have hc_pos : c > 0 := by
      by_contra hc_zero
      have : c = 0 := by omega
      subst this
      omega
    have h_mul : Nat.gcd 2 n * c = 2 := hc.symm
    have : Nat.gcd 2 n ≤ 2 := by
      -- since Nat.gcd 2 n * c = 2 and c >= 1
      nlinarith
    omega
  rcases h_cases with h1 | h2
  · exact h1
  · -- if gcd 2 n = 2, then 2 dvd n, so n % 2 = 0
    have hd := Nat.gcd_dvd_right 2 n
    rw [h2] at hd
    have h_mod : n % 2 = 0 := Nat.mod_eq_zero_of_dvd hd
    omega

theorem divisors_sum_ge_two_divisors (n a b : ℕ) (ha : a ∈ n.divisors) (hb : b ∈ n.divisors) (hab : a ≠ b) : a + b ≤ n.divisors.sum id := by
  have h_subset : {a, b} ⊆ n.divisors := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  have hne : a ∉ ({b} : Finset ℕ) := by
    simp only [mem_singleton]
    exact hab
  have h_sum : ({a, b} : Finset ℕ).sum id = a + b := by
    rw [sum_insert hne, sum_singleton, id_eq, id_eq]
  rw [← h_sum]
  apply sum_le_sum_of_subset h_subset

theorem coprime_three_of_even_deficient (n : ℕ) (hn_even : 2 ∣ n) (hn_def : n.divisors.sum id < 2 * n) (hn2 : 2 ≤ n) : Nat.Coprime 3 n := by
  have h_prime : Nat.Prime 3 := by decide
  rw [Nat.Prime.coprime_iff_not_dvd h_prime]
  intro h_dvd
  -- if 3 ∣ n and 2 ∣ n, then 6 ∣ n
  have h2 : 2 ∣ n := hn_even
  have h3 : 3 ∣ n := h_dvd
  have h6 : 6 ∣ n := by
    have h_co : Nat.Coprime 2 3 := by decide
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd h_co h2 h3
  rcases h6 with ⟨m, rfl⟩
  -- n = 6 * m. Since 2 ≤ n, m ≥ 1
  have hm : m ≥ 1 := by omega
  -- divisors of 6 * m include 6*m, 3*m, 2*m, m
  have hd1 : 6 * m ∈ (6 * m).divisors := by
    rw [mem_divisors]
    exact ⟨dvd_rfl, by omega⟩
  have hd2 : 3 * m ∈ (6 * m).divisors := by
    rw [mem_divisors]
    refine ⟨?_, by omega⟩
    use 2
    ring
  have hd3 : 2 * m ∈ (6 * m).divisors := by
    rw [mem_divisors]
    refine ⟨?_, by omega⟩
    use 3
    ring
  have hd4 : m ∈ (6 * m).divisors := by
    rw [mem_divisors]
    refine ⟨?_, by omega⟩
    use 6
    ring
  -- they are distinct
  have h_dist1 : 6 * m ≠ 3 * m := by omega
  have h_dist2 : 6 * m ≠ 2 * m := by omega
  have h_dist3 : 6 * m ≠ m := by omega
  have h_dist4 : 3 * m ≠ 2 * m := by omega
  have h_dist5 : 3 * m ≠ m := by omega
  have h_dist6 : 2 * m ≠ m := by omega
  -- we can just use a larger subset of size 4
  have h_subset : {6*m, 3*m, 2*m, m} ⊆ (6*m).divisors := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact hd1
    · exact hd2
    · exact hd3
    · exact hd4
  have h_card : ({6*m, 3*m, 2*m, m} : Finset ℕ).sum id = 12 * m := by
    -- we can expand the sum
    have hne1 : 6*m ∉ ({3*m, 2*m, m} : Finset ℕ) := by simp [h_dist1, h_dist2, h_dist3]
    have hne2 : 3*m ∉ ({2*m, m} : Finset ℕ) := by simp [h_dist4, h_dist5]
    have hne3 : 2*m ∉ ({m} : Finset ℕ) := by simp [h_dist6]
    rw [sum_insert hne1, sum_insert hne2, sum_insert hne3, sum_singleton]
    simp only [id_eq]
    ring
  have h_sum_ge : 12 * m ≤ (6*m).divisors.sum id := by
    rw [← h_card]
    apply sum_le_sum_of_subset h_subset
  have h_lt : (6*m).divisors.sum id < 12 * m := by
    have h_calc : 2 * (6 * m) = 12 * m := by ring
    rw [h_calc] at hn_def
    exact hn_def
  omega

theorem even_ge_ten (n : ℕ) (hn_even : 2 ∣ n) (h_not : ¬ (∃ k, n = 2 ^ k)) (hn_def : n.divisors.sum id < 2 * n) (hn2 : 2 ≤ n) (hn3 : ¬ 3 ∣ n) : 10 ≤ n := by
  rcases hn_even with ⟨m, rfl⟩
  have hm : m ≥ 5 := by
    by_contra h_lt
    have : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl
    · omega
    · have hc : ∃ k, 2 = 2^k := ⟨1, by rfl⟩
      exact h_not hc
    · have hc : ∃ k, 4 = 2^k := ⟨2, by rfl⟩
      exact h_not hc
    · have hc : 3 ∣ 6 := ⟨2, by rfl⟩
      exact hn3 hc
    · have hc : ∃ k, 8 = 2^k := ⟨3, by rfl⟩
      exact h_not hc
  omega

theorem divisors_sum_ge_four_divisors (n a b c d : ℕ) (ha : a ∈ n.divisors) (hb : b ∈ n.divisors) (hc : c ∈ n.divisors) (hd : d ∈ n.divisors)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) : a + b + c + d ≤ n.divisors.sum id := by
  have h_subset : {a, b, c, d} ⊆ n.divisors := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
    · exact hd
  have hne1 : a ∉ ({b, c, d} : Finset ℕ) := by simp [hab, hac, had]
  have hne2 : b ∉ ({c, d} : Finset ℕ) := by simp [hbc, hbd]
  have hne3 : c ∉ ({d} : Finset ℕ) := by simp [hcd]
  have h_sum : ({a, b, c, d} : Finset ℕ).sum id = a + b + c + d := by
    rw [sum_insert hne1, sum_insert hne2, sum_insert hne3, sum_singleton, id_eq, id_eq, id_eq, id_eq]
    omega
  rw [← h_sum]
  apply sum_le_sum_of_subset h_subset

theorem divisors_sum_ge_one_point_five_n (n : ℕ) (hn_even : 2 ∣ n) (hn_ge : 10 ≤ n) : 3 * n ≤ 2 * n.divisors.sum id := by
  have h_pos : n > 0 := by omega
  have hd1 : n ∈ n.divisors := by
    rw [mem_divisors]
    exact ⟨dvd_rfl, by omega⟩
  have hd2 : n / 2 ∈ n.divisors := by
    rw [mem_divisors]
    refine ⟨⟨2, by rw [Nat.div_mul_cancel hn_even]⟩, by omega⟩
  have hd3 : 2 ∈ n.divisors := by
    rw [mem_divisors]
    exact ⟨hn_even, by omega⟩
  have hd4 : 1 ∈ n.divisors := by
    rw [mem_divisors]
    exact ⟨one_dvd n, by omega⟩
  have hab : n ≠ n / 2 := by omega
  have hac : n ≠ 2 := by omega
  have had : n ≠ 1 := by omega
  have hbc : n / 2 ≠ 2 := by omega
  have hbd : n / 2 ≠ 1 := by omega
  have hcd : 2 ≠ 1 := by omega
  have h_sum := divisors_sum_ge_four_divisors n n (n/2) 2 1 hd1 hd2 hd3 hd4 hab hac had hbc hbd hcd
  omega

theorem sInf_eq_two_of_mem (s : Set ℕ) (h2 : 2 ∈ s) (h0 : 0 ∉ s) (h1 : 1 ∉ s) : sInf s = 2 := by
  have h_ne : s.Nonempty := ⟨2, h2⟩
  have h_le : ∀ x ∈ s, 2 ≤ x := by
    intro x hx
    cases x with
    | zero => contradiction
    | succ x =>
      cases x with
      | zero =>
        have : 1 ∈ s := hx
        contradiction
      | succ x =>
        omega
  exact le_antisymm (Nat.sInf_le h2) (le_csInf h_ne h_le)

theorem test_coprime_pow (n : ℕ) (hn : n % 2 = 1) (k : ℕ) : Nat.Coprime (2 ^ k) n := by
  have h2 := test_coprime_2 n hn
  exact Nat.Coprime.pow_left k h2

theorem divisors_sum_two_pow (k : ℕ) : (2 ^ k).divisors.sum id = 2 ^ (k + 1) - 1 := by
  have h_prime : Nat.Prime 2 := Nat.prime_two
  rw [sigma1_eq_sigma]
  have h_pow := ArithmeticFunction.sigma_apply_prime_pow (k := 1) (i := k) h_prime
  simp only [mul_one] at h_pow
  rw [h_pow]
  have h_geom := geomSum_eq (m := 2) (by decide) (k + 1)
  rw [h_geom]
  rw [Nat.div_one]

theorem divisors_sum_ge_n_plus_one (n : ℕ) (hn2 : 2 ≤ n) : n + 1 ≤ n.divisors.sum id := by
  have h_pos : n > 0 := by omega
  have h1 : 1 ∈ n.divisors := by
    rw [mem_divisors]
    exact ⟨one_dvd n, Nat.ne_of_gt h_pos⟩
  have hn : n ∈ n.divisors := by
    rw [mem_divisors]
    exact ⟨dvd_rfl, Nat.ne_of_gt h_pos⟩
  have hne : 1 ≠ n := by omega
  have h_ge := divisors_sum_ge_two_divisors n 1 n h1 hn hne
  omega

theorem two_pow_le_two_pow_succ_sub_self (n : ℕ) : n + 1 ≤ 2 ^ (n + 1) := by
  induction n with
  | zero => decide
  | succ n ih =>
    have h_pow : 2 ^ (n + 2) = 2 ^ (n + 1) * 2 := by ring
    rw [h_pow]
    omega

theorem two_pow_mem_S (n : ℕ) (hn : n % 2 = 1) (hn2 : 2 ≤ n) : 2 ^ n ∈ S n := by
  unfold S
  simp only [Set.mem_setOf_eq]
  constructor
  · rw [divisors_sum_two_pow]
    have h_pos : 2 ^ (n + 1) > 0 := pow_pos (by decide) (n + 1)
    have h_eq : 2 * 2 ^ n = 2 ^ (n + 1) := by ring
    rw [h_eq]
    omega
  · have h_coprime := test_coprime_pow n hn n
    rw [sigma1_eq_sigma, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime h_coprime, ← sigma1_eq_sigma, ← sigma1_eq_sigma]
    rw [divisors_sum_two_pow]
    have h_sum := divisors_sum_ge_n_plus_one n hn2
    have h_bound2 := two_pow_le_two_pow_succ_sub_self n
    have h_bound3 : 2 ^ (n + 1) * n + (n + 1) ≤ 2 ^ (n + 1) * (n + 1) := by
      have h_ring : 2 ^ (n + 1) * (n + 1) = 2 ^ (n + 1) * n + 2 ^ (n + 1) := by ring
      rw [h_ring]
      omega
    have h_sub_eq : (2 ^ (n + 1) - 1) * (n + 1) + (n + 1) = 2 ^ (n + 1) * (n + 1) := by
      have h_pos : 2 ^ (n + 1) > 0 := pow_pos (by decide) (n + 1)
      have h_step1 : (2 ^ (n + 1) - 1) * (n + 1) + (n + 1) = (2 ^ (n + 1) - 1) * (n + 1) + 1 * (n + 1) := by rw [one_mul]
      rw [h_step1, ← add_mul]
      rw [Nat.sub_add_cancel h_pos]
    have h_bound : 2 * (2 ^ n * n) ≤ (2 ^ (n + 1) - 1) * (n + 1) := by
      have h_eq : 2 * (2 ^ n * n) = 2 ^ (n + 1) * n := by ring
      rw [h_eq]
      omega
    have h_mono : (2 ^ (n + 1) - 1) * (n + 1) ≤ (2 ^ (n + 1) - 1) * n.divisors.sum id := Nat.mul_le_mul_left (2 ^ (n + 1) - 1) h_sum
    omega


attribute [local instance] Classical.propDecidable

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

theorem prime_divisors_sum {p : ℕ} (hp : Nat.Prime p) : p.divisors.sum id = p + 1 := by
  rw [Nat.Prime.divisors hp]
  have : 1 ≠ p := hp.ne_one.symm
  rw [sum_insert (by simp [this]), sum_singleton, id_eq, id_eq]
  omega

theorem hd_odd_test (d k : ℕ) (h : (d * k) % 2 = 1) : d % 2 = 1 := by
  have h_mul : (d * k) % 2 = (d % 2 * (k % 2)) % 2 := Nat.mul_mod d k 2
  rw [h_mul] at h
  rcases Nat.mod_two_eq_zero_or_one d with hd0 | hd1
  · rw [hd0] at h
    simp only [zero_mul, zero_mod, zero_ne_one] at h
  · exact hd1

theorem divisors_prime_sq {d : ℕ} (hd : Nat.Prime d) : (d * d).divisors = {1, d, d * d} := by
  ext x
  rw [mem_divisors]
  have hd2 : d * d = d ^ 2 := by ring
  have h_ne : d ^ 2 ≠ 0 := pow_ne_zero 2 hd.ne_zero
  rw [hd2]
  simp only [and_iff_left h_ne]
  rw [Nat.dvd_prime_pow hd]
  simp only [mem_insert, mem_singleton]
  constructor
  · rintro ⟨k, hk, rfl⟩
    interval_cases k
    · left; exact pow_zero d
    · right; left; exact pow_one d
    · right; right; ring
  · rintro (rfl | rfl | rfl)
    · refine ⟨0, by decide, (pow_zero d).symm⟩
    · refine ⟨1, by decide, (pow_one x).symm⟩
    · refine ⟨2, by decide, by ring⟩

theorem sum_divisors_prime_sq {d : ℕ} (hd : Nat.Prime d) : (d * d).divisors.sum id = 1 + d + d * d := by
  rw [divisors_prime_sq hd]
  have h1d : 1 ≠ d := hd.ne_one.symm
  have hdm : d ≠ d * d := by
    intro hc
    have h_eq : d * 1 = d * d := by
      rw [mul_one]
      exact hc
    have : 1 = d := Nat.eq_of_mul_eq_mul_left hd.pos h_eq
    omega
  have h1m : 1 ≠ d * d := by
    intro hc
    have : d * d ≥ 2 * 2 := Nat.mul_le_mul hd.two_le hd.two_le
    omega
  rw [sum_insert (by simp [h1d, h1m]), sum_insert (by simp [hdm]), sum_singleton, id_eq, id_eq, id_eq]
  ring

theorem test_minfac (m : ℕ) (hm : m ≥ 3) (hm_odd : m % 2 = 1) :
    Nat.Prime (minFac m) ∧ minFac m ∣ m ∧ minFac m ≥ 3 := by
  have h1 : minFac m ∣ m := minFac_dvd m
  have h_ne : m ≠ 1 := by omega
  have h2 : Nat.Prime (minFac m) := minFac_prime h_ne
  have h3 : minFac m ≥ 3 := by
    have : minFac m ≠ 2 := by
      intro hc
      have : 2 ∣ m := by
        rw [← hc]
        exact h1
      have : m % 2 = 0 := Nat.mod_eq_zero_of_dvd this
      omega
    have : minFac m ≠ 1 := h2.ne_one
    have : minFac m ≠ 0 := h2.ne_zero
    omega
  exact ⟨h2, h1, h3⟩

theorem test_div (m a s_sum : ℕ) (ha : a ≥ 1) (hm : m ≥ 3)
    (h_eq : (2^(a+1) - 1) * s_sum = 2^(a+1) * m - 1) : (2^(a+1) - 1) ∣ (m - 1) := by
  have h_pow_ge : 2^(a+1) ≥ 4 := by
    have h_exp : a + 1 ≥ 2 := by omega
    have h_two : 2^2 ≤ 2^(a+1) := Nat.pow_le_pow_right (by decide) h_exp
    exact h_two
  have h_pow_pos : 2^(a+1) * m ≥ m := by
    have : 2^(a+1) ≥ 1 := by omega
    exact Nat.le_mul_of_pos_left m (by omega)
  have h_eq2 : 2^(a+1) * m - 1 = (2^(a+1) - 1) * m + (m - 1) := by
    rw [Nat.sub_mul, one_mul]
    omega
  have h_div : (2^(a+1) - 1) ∣ (2^(a+1) - 1) * m + (m - 1) := by
    use s_sum
    rw [h_eq]
    exact h_eq2.symm
  have h_self : (2^(a+1) - 1) ∣ (2^(a+1) - 1) * m := dvd_mul_right (2^(a+1) - 1) m
  exact (Nat.dvd_add_iff_right h_self).mpr h_div

theorem test_c_even (m a c : ℕ) (hm_odd : m % 2 = 1) (hm : m ≥ 3) (ha : a ≥ 1)
    (hc : m - 1 = (2^(a+1) - 1) * c) : c % 2 = 0 := by
  by_contra hc_odd
  have hc_odd' : c % 2 = 1 := by omega
  have h_pow_even : 2^(a+1) % 2 = 0 := by
    rw [pow_succ]
    rw [Nat.mul_mod]
    simp
  have h_pow_ge : 2^(a+1) ≥ 2 := by
    have h_exp : a + 1 ≥ 2 := by omega
    have h_two : 2^2 ≤ 2^(a+1) := Nat.pow_le_pow_right (by decide) h_exp
    omega
  have h_pow_odd : (2^(a+1) - 1) % 2 = 1 := by
    omega
  have h_prod : ((2^(a+1) - 1) * c) % 2 = 1 := by
    rw [Nat.mul_mod, h_pow_odd, hc_odd']
  have h_even : (m - 1) % 2 = 0 := by omega
  omega

theorem test_formula_derivation (Y k s_sum : ℕ) (h_pow_ge : Y ≥ 4)
    (h_eq : Y * ((Y - 1) * (2 * k) + 1) = (Y - 1) * s_sum + 1) :
    s_sum = 2 * k * Y + 1 := by
  have h_rw : Y * ((Y - 1) * (2 * k) + 1) = (Y - 1) * (2 * k * Y) + Y := by
    have h_mul : Y * ((Y - 1) * (2 * k) + 1) = Y * ((Y - 1) * (2 * k)) + Y := by ring
    rw [h_mul]
    congr 1
    ring
  rw [h_rw] at h_eq
  have h_eq2 : (Y - 1) * (2 * k * Y) + Y = (Y - 1) * (2 * k * Y + 1) + 1 := by
    rw [mul_add, mul_one]
    omega
  rw [h_eq2] at h_eq
  have h_eq3 : (Y - 1) * (2 * k * Y + 1) = (Y - 1) * s_sum := by omega
  have h_Y_sub_ne : Y - 1 ≠ 0 := by omega
  exact (Nat.mul_right_inj h_Y_sub_ne).mp h_eq3.symm

theorem test_sum_mk (Y k m s_sum : ℕ) (h_pow_ge : Y ≥ 4)
    (h_deriv : s_sum = 2 * k * Y + 1)
    (h_m_eq : m = (Y - 1) * (2 * k) + 1) : s_sum = m + 2 * k := by
  rw [h_deriv, h_m_eq]
  have h_sub : (Y - 1) * (2 * k) = Y * (2 * k) - 2 * k := by
    rw [Nat.sub_mul, one_mul]
  rw [h_sub]
  have : Y * (2 * k) ≥ 2 * k := by
    have : Y ≥ 1 := by omega
    exact Nat.le_mul_of_pos_left (2 * k) (by omega)
  have h_ring : 2 * k * Y = Y * (2 * k) := by ring
  rw [h_ring]
  omega

theorem test_prime_D_one (m a : ℕ) (hm_odd : m % 2 = 1) (hp : Nat.Prime m) (h_sum : m.divisors.sum id = m + 1)
    (h_D : 2^(a+1) * m - (2^(a+1) - 1) * m.divisors.sum id = 1) : False := by
  rw [h_sum] at h_D
  generalize hX : 2^(a+1) = X
  rw [hX] at h_D
  have h_eq : X * m = (X - 1) * (m + 1) + 1 := by omega
  have h_ring : (X - 1) * (m + 1) + 1 = X * m + X - m := by
    have h_pow_pos : X ≥ 1 := by
      have : X > 0 := by
        rw [← hX]
        positivity
      omega
    have h_eq2 : (X - 1) * (m + 1) + (m + 1) = X * (m + 1) := by
      have h_one : (X - 1) * (m + 1) + (m + 1) = (X - 1) * (m + 1) + 1 * (m + 1) := by rw [one_mul]
      rw [h_one, ← add_mul]
      rw [Nat.sub_add_cancel h_pow_pos]
    have h_expand1 : (X - 1) * (m + 1) + (m + 1) = (X - 1) * (m + 1) + m + 1 := by ring
    have h_expand2 : X * (m + 1) = X * m + X := by ring
    rw [h_expand1] at h_eq2
    omega
  rw [h_ring] at h_eq
  have hp_eq : m = X := by omega
  have hp_even : m % 2 = 0 := by
    rw [hp_eq, ← hX]
    rw [pow_succ]
    simp
  omega

theorem h_sum_ne2 {m : ℕ} (hm_odd : m % 2 = 1) (hm_ge : m ≥ 3) : m.divisors.sum id ≠ 2 * m - 1 := by
  intro h_sum
  by_cases hp : Nat.Prime m
  · have : m.divisors.sum id = m + 1 := prime_divisors_sum hp
    omega
  · have hm_ge2 : 2 ≤ m := by omega
    let d := minFac m
    have hd_prime : Nat.Prime d := Nat.minFac_prime (by omega)
    have hd : d ∣ m := minFac_dvd m
    have hd_ge2 : 2 ≤ d := hd_prime.two_le
    have hd_le : d ≤ m := Nat.le_of_dvd (by omega) hd
    have hd_ne : d ≠ m := by
      intro hc
      have : Nat.Prime m := by rwa [← hc]
      exact hp this
    have hd_lt : d < m := lt_of_le_of_ne hd_le hd_ne
    have hd_odd : d % 2 = 1 := hd_odd_test d (m/d) (by rwa [← Nat.mul_div_cancel' hd] at hm_odd)
    have hd_ge3 : d ≥ 3 := by omega
    have hd_div : m/d ∣ m := Nat.div_dvd_of_dvd hd
    have hd_div_ge3 : m/d ≥ 3 := by
      generalize hk : m / d = k
      have : k ≠ 1 := by
        intro hc
        have : m = d := by
          rw [← Nat.div_mul_cancel hd, hk, hc, one_mul]
        omega
      have : k ≠ 0 := by
        intro hc
        have : m = 0 := by
          rw [← Nat.div_mul_cancel hd, hk, hc, zero_mul]
        omega
      have h_odd2 : k % 2 = 1 := by
        rw [← hk]
        exact hd_odd_test (m/d) d (by rwa [← Nat.div_mul_cancel hd] at hm_odd)
      have : k ≠ 2 := by
        intro hc
        rw [hc] at h_odd2
        contradiction
      omega
    by_cases hd_eq : d = m/d
    · have : m = d * d := by
        have h_eq : m = (m / d) * d := (Nat.div_mul_cancel hd).symm
        rw [← hd_eq] at h_eq
        exact h_eq
      have h_sum_sq : m.divisors.sum id = 1 + d + d * d := by
        rw [this]
        exact sum_divisors_prime_sq hd_prime
      have h_sum' : 1 + d + d * d = 2 * (d * d) - 1 := by
        rwa [h_sum_sq, this] at h_sum
      have h_alg : d * d = d + 2 := by omega
      have h_ge : 3 * d > d + 2 := by omega
      have h_le : d * d ≥ 3 * d := Nat.mul_le_mul_right d hd_ge3
      omega
    · have h1 : 1 ∈ m.divisors := by
        rw [mem_divisors]
        exact ⟨one_dvd m, by omega⟩
      have h_d : d ∈ m.divisors := by
        rw [mem_divisors]
        exact ⟨hd, by omega⟩
      have h_md : m/d ∈ m.divisors := by
        rw [mem_divisors]
        exact ⟨hd_div, by omega⟩
      have hm : m ∈ m.divisors := by
        rw [mem_divisors]
        exact ⟨dvd_rfl, by omega⟩
      have h1d : 1 ≠ d := by omega
      have h1md : 1 ≠ m/d := by omega
      have h1m : 1 ≠ m := by omega
      have hdm : d ≠ m := by omega
      have hmdm : m/d ≠ m := by
        intro hc
        have : m = (m/d) * d := (Nat.div_mul_cancel hd).symm
        rw [hc] at this
        have h_eq' : m * 1 = m * d := by
          rw [mul_one]
          exact this
        have h_m_pos : m > 0 := by omega
        have : 1 = d := Nat.eq_of_mul_eq_mul_left h_m_pos h_eq'
        omega
      have h_sub : {1, d, m/d, m} ⊆ m.divisors := by
        intro x hx
        simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl | rfl | rfl
        · exact h1
        · exact h_d
        · exact h_md
        · exact hm
      have h_sum_ge : 1 + d + m/d + m ≤ m.divisors.sum id := by
        have h_sum_four : ({1, d, m/d, m} : Finset ℕ).sum id = 1 + d + m/d + m := by
          rw [sum_insert (by simp [h1d, h1md, h1m]), sum_insert (by simp [hd_eq, hdm]), sum_insert (by simp [hmdm]), sum_singleton, id_eq, id_eq, id_eq, id_eq]
          omega
        rw [← h_sum_four]
        exact sum_le_sum_of_subset h_sub
      have h_eq : d * (m/d) = (d - 1) * (m/d - 1) + (d - 1) + (m/d - 1) + 1 := by
        have hd_eq : d = (d - 1) + 1 := (Nat.sub_add_cancel (by omega)).symm
        have hX_eq : m/d = (m/d - 1) + 1 := (Nat.sub_add_cancel (by omega)).symm
        nth_rw 1 [hd_eq]
        nth_rw 1 [hX_eq]
        ring
      have h_le : (d - 1) * (m/d - 1) ≥ 4 := by
        have h1 : d - 1 ≥ 2 := by omega
        have h2 : m/d - 1 ≥ 2 := by omega
        exact Nat.mul_le_mul h1 h2
      have hd_eq' : d = (d - 1) + 1 := (Nat.sub_add_cancel (by omega)).symm
      have hX_eq' : m/d = (m/d - 1) + 1 := (Nat.sub_add_cancel (by omega)).symm
      have hm_eq : m = (d - 1) * (m/d - 1) + (d - 1) + (m/d - 1) + 1 := by
        have : m = d * (m/d) := by
          rw [mul_comm]
          exact (Nat.div_mul_cancel hd).symm
        rw [this, h_eq]
      rw [hX_eq', hd_eq'] at h_sum_ge
      omega

theorem D_ne_one (m a : ℕ) (hm_odd : m % 2 = 1) (hm_ge : m ≥ 3) (hp : ¬Nat.Prime m)
    (h_sum_ne2 : m.divisors.sum id ≠ 2 * m - 1)
    (h_D : 2^(a+1) * m - (2^(a+1) - 1) * m.divisors.sum id = 1) : False := by
  by_cases ha0 : a = 0
  · subst ha0
    simp only [zero_add, pow_one] at h_D
    have : m.divisors.sum id = 2 * m - 1 := by omega
    exact h_sum_ne2 this
  · have ha : a ≥ 1 := by omega
    have h_pow_ge : 2^(a+1) ≥ 4 := by
      have h_exp : a + 1 ≥ 2 := by omega
      have h_two : 2^2 ≤ 2^(a+1) := Nat.pow_le_pow_right (by decide) h_exp
      exact h_two
    have h_eq : (2^(a+1) - 1) * m.divisors.sum id = 2^(a+1) * m - 1 := by omega
    have h_div := test_div m a (m.divisors.sum id) ha hm_ge h_eq
    rcases h_div with ⟨c, hc⟩
    have hc_even : c % 2 = 0 := test_c_even m a c hm_odd hm_ge ha hc
    have h_dvd_c : 2 ∣ c := dvd_of_mod_eq_zero hc_even
    rcases h_dvd_c with ⟨k, rfl⟩
    have h_eq_add : 2^(a+1) * m = (2^(a+1) - 1) * m.divisors.sum id + 1 := by omega
    have h_m_eq : m = (2^(a+1) - 1) * (2 * k) + 1 := by omega
    have h_eq_add' : 2^(a+1) * ((2^(a+1) - 1) * (2 * k) + 1) = (2^(a+1) - 1) * m.divisors.sum id + 1 := by
      calc 2^(a+1) * ((2^(a+1) - 1) * (2 * k) + 1)
        _ = 2^(a+1) * m := by rw [h_m_eq]
        _ = (2^(a+1) - 1) * m.divisors.sum id + 1 := h_eq_add
    have h_deriv := test_formula_derivation (2^(a+1)) k (m.divisors.sum id) h_pow_ge h_eq_add'
    rcases test_minfac m hm_ge hm_odd with ⟨hp_p, hd_p, hp_ge3⟩
    have h_prime_p : Nat.Prime (minFac m) := hp_p
    have hd_p : minFac m ∣ m := hd_p
    have hp_ge3 : minFac m ≥ 3 := hp_ge3
    let p := minFac m
    have h_pd : p * (m / p) = m := Nat.mul_div_cancel' hd_p
    generalize hd_eq : m / p = d
    rw [hd_eq] at h_pd
    have hd_dvd : d ∣ m := by
      use p
      rw [mul_comm]
      exact h_pd.symm
    have hp_ne_m : p ≠ m := by
      intro hc_pm
      have : minFac m = m := hc_pm
      rw [this] at h_prime_p
      exact hp h_prime_p
    have hd_gt1 : d ≥ 2 := by
      have hd1' : d ≠ 1 := by
        intro hc
        have h_pm : p = m := by
          rw [hc, mul_one] at h_pd
          exact h_pd
        exact hp_ne_m h_pm
      have hd0 : d ≠ 0 := by
        intro hc
        have h_zero : p * 0 = 0 := mul_zero p
        have : 0 = m := by
          rw [← h_zero]
          rw [← hc]
          exact h_pd
        omega
      omega
    have hd_lt_m : d < m := by
      have : 3 * d ≤ p * d := Nat.mul_le_mul_right d hp_ge3
      rw [h_pd] at this
      omega
    have hp_odd : p % 2 = 1 := hd_odd_test p d (by rwa [← h_pd] at hm_odd)
    have h_sum_mk := test_sum_mk (2^(a+1)) k m (m.divisors.sum id) h_pow_ge h_deriv h_m_eq
    have hp_ne_d : p ≠ d := by
      intro hc
      have h_sum_sq : m.divisors.sum id = 1 + p + p * p := by
        have h_eq : m = p * p := by
          rw [← hc] at h_pd
          exact h_pd.symm
        rw [h_eq]
        exact sum_divisors_prime_sq h_prime_p
      have h_2k : 2 * k = p + 1 := by
        have h_sum_mk' := h_sum_mk
        rw [h_sum_sq] at h_sum_mk'
        have h_eq : m = p * p := by
          rw [← hc] at h_pd
          exact h_pd.symm
        rw [h_eq] at h_sum_mk'
        omega
      have h_alg : p * p = (2^(a+1) - 1) * (p + 1) + 1 := by
        have h_m_eq' := h_m_eq
        have h_eq : m = p * p := by
          rw [← hc] at h_pd
          exact h_pd.symm
        rw [h_eq] at h_m_eq'
        rw [h_2k] at h_m_eq'
        exact h_m_eq'
      have h_alg2 : p * (p + 1) = 2^(a+1) * (p + 1) := by
        have h_sub_mul : (2^(a+1) - 1) * (p + 1) = 2^(a+1) * (p + 1) - (p + 1) := by
          rw [Nat.sub_mul, one_mul]
        rw [h_sub_mul] at h_alg
        have h_pos : 2^(a+1) * (p + 1) ≥ p + 1 := Nat.le_mul_of_pos_left (p + 1) (by positivity)
        have h_ring_id : p * p + p + 1 = p * (p + 1) + 1 := by ring
        omega
      have hp_eq : p = 2^(a+1) := Nat.eq_of_mul_eq_mul_right (by omega) h_alg2
      have hp_even : p % 2 = 0 := by
        rw [hp_eq]
        rw [pow_succ]
        simp
      omega
    have hd_odd : d % 2 = 1 := hd_odd_test d p (by rwa [← h_pd, mul_comm] at hm_odd)
    have hd1 : 1 ∈ m.divisors := by rw [mem_divisors]; exact ⟨one_dvd m, by omega⟩
    have h_p : p ∈ m.divisors := by rw [mem_divisors]; exact ⟨hd_p, by omega⟩
    have h_d : d ∈ m.divisors := by rw [mem_divisors]; exact ⟨hd_dvd, by omega⟩
    have hm : m ∈ m.divisors := by rw [mem_divisors]; exact ⟨dvd_rfl, by omega⟩
    have h1p : 1 ≠ p := by omega
    have h1d : 1 ≠ d := by omega
    have hpd : p ≠ d := hp_ne_d
    have hpm : p ≠ m := hp_ne_m
    have hdm : d ≠ m := by omega
    have h1m : 1 ≠ m := by omega
    have h_sub : {1, p, d, m} ⊆ m.divisors := by
      intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact hd1
      · exact h_p
      · exact h_d
      · exact hm
    have h_sum_ge : 1 + p + d + m ≤ m.divisors.sum id := by
      have h_sum_four : ({1, p, d, m} : Finset ℕ).sum id = 1 + p + d + m := by
        rw [sum_insert (by simp [h1p, h1d, h1m]), sum_insert (by simp [hpd, hpm]), sum_insert (by simp [hdm]), sum_singleton, id_eq, id_eq, id_eq, id_eq]
        omega
      rw [← h_sum_four]
      exact sum_le_sum_of_subset h_sub
    have h_3d_le : 3 * d ≤ m := by
      have : 3 * d ≤ p * d := Nat.mul_le_mul_right d hp_ge3
      rw [h_pd] at this
      exact this
    have h_bound1 : m ≥ 6 * k + 1 := by
      have : 2^(a+1) - 1 ≥ 3 := by omega
      nlinarith
    have h_2k_ge : 2 * k ≥ p + d + 2 := by
      have h_ge : 2 * k ≥ p + d + 1 := by omega
      have h_ne : 2 * k ≠ p + d + 1 := by
        intro hc
        have h_even : (2 * k) % 2 = 0 := by simp
        have h_odd : (p + d + 1) % 2 = 1 := by omega
        omega
      omega
    by_cases hp3 : p = 3
    · omega
    · have hp_ge5 : p ≥ 5 := by omega
      have hd_ge5 : d ≥ 5 := by
        by_cases hd_pr : Nat.Prime d
        · have : d > p := by
            have : d ≥ p := by
              have hd_dvd' : d ∣ m := hd_dvd
              have : minFac m ≤ d := Nat.minFac_le_of_dvd (by omega) hd_dvd'
              exact this
            omega
          omega
        · have hd_ge2 : d ≥ 2 := by omega
          let q := minFac d
          have hq_pr : Nat.Prime q := Nat.minFac_prime (by omega)
          have hq_dvd : q ∣ d := minFac_dvd d
          have hq_dvd_m : q ∣ m := dvd_trans hq_dvd hd_dvd
          have hp_le_q : p ≤ q := Nat.minFac_le_of_dvd (by omega) hq_dvd_m
          have hd_div_q_ge3 : d / q ≥ 3 := by
            have h_ne1 : d / q ≠ 1 := by
              intro hc
              have : d = q := by
                rw [← Nat.div_mul_cancel hq_dvd, hc, one_mul]
              have : Nat.Prime d := by rwa [this]
              contradiction
            have h_ne0 : d / q ≠ 0 := by
              intro hc
              have : d = 0 := by
                rw [← Nat.div_mul_cancel hq_dvd, hc, zero_mul]
              omega
            have h_odd_div : (d / q) % 2 = 1 := hd_odd_test (d / q) q (by rwa [← Nat.div_mul_cancel hq_dvd] at hd_odd)
            have h_ne2 : d / q ≠ 2 := by
              intro hc
              rw [hc] at h_odd_div
              contradiction
            clear h_sub h_sum_ge h_3d_le h_bound1 h_2k_ge hp_ge5
            omega
          have : d = q * (d / q) := by
            rw [mul_comm]
            exact (Nat.div_mul_cancel hq_dvd).symm
          nlinarith
      omega
theorem S_le_two_pow (n : ℕ) (hn : 2 ≤ n) (h_non_def : ¬2 * n ≤ n.divisors.sum id) (hn_even : ¬2 ∣ n) (h_two_pow : ∃ x, 2^x ∈ S n) (k : ℕ) (hk : k ∈ S n) :
    2 ^ (Nat.find h_two_pow) ≤ k := by
  let s := Nat.find h_two_pow
  by_cases hk_pow : ∃ j, k = 2 ^ j
  · rcases hk_pow with ⟨j, rfl⟩
    have hs_min : ∀ i < Nat.find h_two_pow, 2^i ∉ S n := fun i hi => Nat.find_min h_two_pow hi
    by_contra h_lt
    have h_lt' : j < Nat.find h_two_pow := by
      have h_pos : 2 > 1 := by decide
      exact (Nat.pow_lt_pow_iff_right h_pos).mp (not_le.mp h_lt)
    have := hs_min j h_lt'
    contradiction
  · by_contra h_lt
    have hk_pos : k ≠ 0 := by
      intro h_zero
      subst h_zero
      unfold S at hk
      simp at hk
    rcases ord_two_and_odd k hk_pos with ⟨a, m, rfl, hm_odd⟩
    have hm_ne_one : m ≠ 1 := by
      intro h_one
      subst h_one
      simp only [mul_one] at hk_pow
      exact hk_pow ⟨a, rfl⟩
    have hm_ge_three : m ≥ 3 := by
      rcases Nat.mod_two_eq_zero_or_one m with h_zero | h_one
      · omega
      · omega
    have ha_lt : a + 2 ≤ s := by
      have h_pow : 2^(a+1) < 2^s := by
        have h_pow_succ : 2^(a+1) = 2^a * 2 := by rw [pow_succ]
        rw [h_pow_succ]
        have h_trans : 2^a * 2 < 2^a * m := by
          have h_m : 2 < m := by omega
          exact Nat.mul_lt_mul_of_pos_left h_m (pow_pos (by decide) a)
        exact lt_trans h_trans (not_le.mp h_lt)
      omega
    have h_s_ge_one : s ≥ 1 := by omega
    have hs_min : ∀ i < Nat.find h_two_pow, 2^i ∉ S n := fun i hi => Nat.find_min h_two_pow hi
    have h_s_sub_one_not : 2^(s-1) ∉ S n := by
      exact hs_min (Nat.find h_two_pow - 1) (by omega)
    have hn_odd : n % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one n with h_zero | h_one
      · have : 2 ∣ n := dvd_of_mod_eq_zero h_zero
        contradiction
      · exact h_one
    have h_cop_s : Nat.Coprime (2 ^ (s - 1)) n := coprime_pow_two_odd (s - 1) n hn_odd
    have h_mult_s : (2^(s-1) * n).divisors.sum id = (2^(s-1)).divisors.sum id * n.divisors.sum id := by
      rw [sigma1_eq_sigma, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime h_cop_s, ← sigma1_eq_sigma, ← sigma1_eq_sigma]
    have h_s_not_S : 2 * (2^(s-1) * n) > (2^(s-1) * n).divisors.sum id := by
      by_contra hc
      have hc_le : 2 * (2^(s-1) * n) ≤ (2^(s-1) * n).divisors.sum id := Nat.le_of_not_lt hc
      have h_S_mem : 2^(s-1) ∈ S n := by
        unfold S
        simp only [Set.mem_setOf_eq]
        constructor
        · rw [divisors_sum_two_pow]
          have h_eq_pow : 2 * 2 ^ (s - 1) = 2 ^ s := by
            rw [mul_comm, ← pow_succ, Nat.sub_add_cancel h_s_ge_one]
          rw [h_eq_pow]
          have h_pos : 2^s > 0 := pow_pos (by decide) s
          omega
        · exact hc_le
      exact h_s_sub_one_not h_S_mem
    have h_eq_pow : 2 * 2 ^ (s - 1) = 2 ^ s := by
      rw [mul_comm, ← pow_succ, Nat.sub_add_cancel h_s_ge_one]
    have h_eq_pow2 : 2 * (2 ^ (s - 1) * n) = 2^s * n := by
      rw [← mul_assoc, h_eq_pow]
    have h_S_ge_n : n.divisors.sum id ≥ n := by
      have h_sum := divisors_sum_ge_n_plus_one n hn
      omega
    have h_pow_s_ge_one : 2^s ≥ 1 := by
      have : s ≥ 1 := h_s_ge_one
      have : 2^1 ≤ 2^s := Nat.pow_le_pow_right (by decide) this
      omega
    have h_term1 : 2^s * n.divisors.sum id ≥ n.divisors.sum id := by
      have := Nat.mul_le_mul_right (n.divisors.sum id) h_pow_s_ge_one
      rw [one_mul] at this
      exact this
    have h_term2 : 2^s * n.divisors.sum id - n.divisors.sum id < 2^s * n := by
      rw [h_eq_pow2] at h_s_not_S
      rw [h_mult_s, divisors_sum_two_pow, Nat.sub_add_cancel h_s_ge_one] at h_s_not_S
      have h_ring : (2^s - 1) * n.divisors.sum id = 2^s * n.divisors.sum id - n.divisors.sum id := by
        rw [Nat.sub_mul, one_mul]
      rw [← h_ring]
      exact h_s_not_S
    have h_term3 : 2^s * n.divisors.sum id < 2^s * n + n.divisors.sum id := by omega
    have h_term4 : 2^s * n.divisors.sum id - 2^s * n < n.divisors.sum id := by omega
    have h_diff : n.divisors.sum id > 2^s * (n.divisors.sum id - n) := by
      rw [Nat.mul_sub_left_distrib]
      exact h_term4

    unfold S at hk
    simp only [Set.mem_setOf_eq] at hk
    have hk_sum := hk.1
    have hk_sum_n := hk.2
    have h_cop : Nat.Coprime (2 ^ a) m := coprime_pow_two_odd a m hm_odd
    have h_mult : (2 ^ a * m).divisors.sum id = (2 ^ a).divisors.sum id * m.divisors.sum id := by
      rw [sigma1_eq_sigma, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime h_cop, ← sigma1_eq_sigma, ← sigma1_eq_sigma]
    rw [h_mult, divisors_sum_two_pow] at hk_sum
    have h_mult2 : (2^a * m * n).divisors.sum id ≤ (2^a * m).divisors.sum id * n.divisors.sum id := divisors_sum_mul_le (2^a * m) n
    have hk_sum_n_le : 2 * (2^a * m * n) ≤ (2^(a+1) - 1) * m.divisors.sum id * n.divisors.sum id := by
      rw [h_mult, divisors_sum_two_pow] at h_mult2
      omega
    have h_ring : 2 * (2 ^ a * m) * n = 2 ^ (a + 1) * m * n := by
      rw [← mul_assoc, mul_comm 2 (2^a), ← pow_succ]
    have hk_sum_n_le2 : 2^(a+1) * m * n ≤ (2^(a+1) - 1) * m.divisors.sum id * n.divisors.sum id := by
      have h_assoc : 2 * (2 ^ a * m * n) = 2 * (2 ^ a * m) * n := by ring
      rw [← h_ring, ← h_assoc]
      exact hk_sum_n_le
    have hk_sum_rew : (2^(a+1) - 1) * m.divisors.sum id < 2^(a+1) * m := by
      have h_eq : 2 * (2^a * m) = 2^(a+1) * m := by
        rw [← mul_assoc, mul_comm 2 (2^a), ← pow_succ]
      rw [h_eq] at hk_sum
      exact hk_sum
    have h_calc2 : (2^(a+1) - 1) * m.divisors.sum id ≤ 2^(a+1) * m - 1 := by
      exact Nat.le_sub_one_of_lt hk_sum_rew
    have h_D : 2^(a+1) * m - (2^(a+1) - 1) * m.divisors.sum id ≥ 1 := by
      have h_pos : 2^(a+1) > 0 := pow_pos (by decide) (a + 1)
      have h_ge : m + 1 ≤ m.divisors.sum id := divisors_sum_ge_n_plus_one m (by omega)
      omega
    generalize h_D_eq : 2^(a+1) * m - (2^(a+1) - 1) * m.divisors.sum id = D
    have h_D_ge_one : D ≥ 1 := by
      rw [← h_D_eq]
      exact h_D
    have h_D_calc : D * n.divisors.sum id ≤ 2^(a+1) * m * (n.divisors.sum id - n) := by
      have h_eq_D : (2^(a+1) - 1) * m.divisors.sum id = 2^(a+1) * m - D := by
        have h_le_B : (2^(a+1) - 1) * m.divisors.sum id ≤ 2^(a+1) * m := le_trans h_calc2 (Nat.sub_le _ _)
        omega
      have h_step3 : 2^(a+1) * m * n ≤ (2^(a+1) * m - D) * n.divisors.sum id := by
        have h_temp := hk_sum_n_le2
        rw [h_eq_D] at h_temp
        exact h_temp
      have h_step4 : (2^(a+1) * m - D) * n.divisors.sum id = 2^(a+1) * m * n.divisors.sum id - D * n.divisors.sum id := by
        rw [Nat.sub_mul]
      rw [h_step4] at h_step3
      have h_D_le_A : D ≤ 2^(a+1) * m := by
        rw [← h_D_eq]
        exact Nat.sub_le _ _
      have h_le_C : D * n.divisors.sum id ≤ 2^(a+1) * m * n.divisors.sum id := Nat.mul_le_mul_right (n.divisors.sum id) h_D_le_A
      have h_le_sub : D * n.divisors.sum id + 2^(a+1) * m * n ≤ 2^(a+1) * m * n.divisors.sum id := by
        rw [Nat.add_comm]
        exact Nat.add_le_of_le_sub h_le_C h_step3
      have h_step5 : D * n.divisors.sum id ≤ 2^(a+1) * m * n.divisors.sum id - 2^(a+1) * m * n := Nat.le_sub_of_add_le h_le_sub
      rw [Nat.mul_sub_left_distrib]
      exact h_step5
    have h_trans_final : D * (2^s * (n.divisors.sum id - n)) < D * n.divisors.sum id := by
      have h_step5 : 2^s * (n.divisors.sum id - n) < n.divisors.sum id := h_diff
      exact Nat.mul_lt_mul_of_pos_left h_step5 h_D_ge_one
    have h_final_bound : D * 2^s < 2^(a+1) * m := by
      have h_sum_ge : 2 ≤ n := hn
      have h_ge2 := divisors_sum_ge_n_plus_one n h_sum_ge
      have h_diff_pos : n.divisors.sum id - n ≥ 1 := by omega
      have h_step7 : D * (2^s * (n.divisors.sum id - n)) < 2^(a+1) * m * (n.divisors.sum id - n) := lt_of_lt_of_le h_trans_final h_D_calc
      rw [← mul_assoc] at h_step7
      exact Nat.lt_of_mul_lt_mul_right h_step7
    have h_final_bound2 : D * 2^(s - a - 1) < m := by
      have h_pow_eq_s : 2^s = 2^(a+1) * 2^(s - a - 1) := by
        clear h_D_eq h_D_ge_one h_D h_D_calc h_trans_final h_final_bound D
        rw [← pow_add]
        congr 1
        dsimp [s] at *
        omega
      rw [h_pow_eq_s] at h_final_bound
      have h_ring : D * (2^(a+1) * 2^(s - a - 1)) = 2^(a+1) * (D * 2^(s - a - 1)) := by ring
      rw [h_ring] at h_final_bound
      have h_pow_pos : 2^(a+1) > 0 := pow_pos (by decide) (a + 1)
      exact Nat.lt_of_mul_lt_mul_left h_final_bound
    generalize h_L_eq : 2^(s - a - 1) = L
    have h_L_ge : L ≥ 2 := by
      rw [← h_L_eq]
      have : s - a - 1 ≥ 1 := by omega
      have h_pow_le : 2^1 ≤ 2^(s - a - 1) := Nat.pow_le_pow_right (by decide) this
      omega
    have h_DL : D * L < m := by
      rw [← h_L_eq]
      exact h_final_bound2
    have h_L_le_DL : L ≤ D * L := by
      calc L = 1 * L := by rw [one_mul]
           _ ≤ D * L := Nat.mul_le_mul_right L h_D_ge_one
    have h_L_lt_m : L < m := lt_of_le_of_lt h_L_le_DL h_DL
    have h_D_le_val : D ≤ m + 1 - 2^(a+1) := by
      rw [← h_D_eq]
      have h_ge : m + 1 ≤ m.divisors.sum id := divisors_sum_ge_n_plus_one m (by omega)
      have h_step8 : (2^(a+1) - 1) * (m + 1) ≤ (2^(a+1) - 1) * m.divisors.sum id := Nat.mul_le_mul_left (2^(a+1) - 1) h_ge
      have h_ring2 : (2^(a+1) - 1) * (m + 1) = 2^(a+1) * m + 2^(a+1) - m - 1 := by
        have h_pos : 2^(a+1) > 0 := pow_pos (by decide) (a + 1)
        rw [Nat.sub_mul, one_mul, mul_add, mul_one]
        omega
      omega

    by_cases h_cases : s - a - 1 ≥ a + 1
    · have h_L_ge2 : L ≥ 2^(a+1) := by
        rw [← h_L_eq]
        exact Nat.pow_le_pow_right (by decide) h_cases
      have h_L_sub_ge : L - 1 ≥ 2^(a+1) - 1 := by omega
      have h_m_lt : m < 2 * L := by
        have h_pow_eq : 2^s = 2^a * (2 * L) := by
          rw [← h_L_eq]
          rw [← mul_assoc, ← pow_succ]
          rw [← pow_add]
          congr 1
          omega
        have h_lt_rew := h_lt
        rw [h_pow_eq] at h_lt_rew
        have h_lt_pos := not_le.mp h_lt_rew
        exact Nat.lt_of_mul_lt_mul_left h_lt_pos
      by_cases h_D_ge_two : D ≥ 2
      · have h_DL_ge : D * L ≥ 2 * L := Nat.mul_le_mul_right L h_D_ge_two
        omega
      · have h_D_one : D = 1 := by omega
        by_cases hp : Nat.Prime m
        · have h_sum_pr : m.divisors.sum id = m + 1 := prime_divisors_sum hp
          have h_false : False := test_prime_D_one m a hm_odd hp h_sum_pr h_D_one
          exact False.elim h_false
        · have h_sum_ne2' : m.divisors.sum id ≠ 2 * m - 1 := h_sum_ne2 hm_odd hm_ge_three
          have h_false : False := D_ne_one m a hm_odd hm_ge_three hp h_sum_ne2' h_D_one
          exact False.elim h_false
    · clear D h_D_ge_one h_D h_D_calc h_trans_final h_final_bound h_final_bound2 h_L_ge h_DL h_L_lt_m h_L_le_DL h_D_le_val L h_L_eq h_D_eq
      have h_s_le : s ≤ 2 * a + 1 := by omega
      have h_ge_m : m + 1 ≤ m.divisors.sum id := divisors_sum_ge_n_plus_one m (by omega)
      have h_lt_m : (2^(a+1) - 1) * (m + 1) < 2^(a+1) * m := by
        calc (2^(a+1) - 1) * (m + 1)
          _ ≤ (2^(a+1) - 1) * m.divisors.sum id := Nat.mul_le_mul_left _ h_ge_m
          _ < 2^(a+1) * m := hk_sum_rew
      have h_ring_m : (2^(a+1) - 1) * (m + 1) + m + 1 = 2^(a+1) * m + 2^(a+1) := by
        have h_pos : 2^(a+1) > 0 := pow_pos (by decide) (a+1)
        have h_step1 : (2^(a+1) - 1) * (m + 1) + 1 * (m + 1) = 2^(a+1) * (m + 1) := by
          rw [← add_mul, Nat.sub_add_cancel h_pos]
        rw [one_mul] at h_step1
        have h_step2 : 2^(a+1) * (m + 1) = 2^(a+1) * m + 2^(a+1) := by ring
        omega
      have h_le_m : 2^(a+1) ≤ m := by
        have h_pos : 2^(a+1) > 0 := pow_pos (by decide) (a+1)
        omega
      have h_ne_m : m ≠ 2^(a+1) := by
        intro hc
        have h_mod1 : m % 2 = 1 := hm_odd
        have h_mod2 : (2^(a+1)) % 2 = 0 := by
          rw [pow_succ]
          exact Nat.mul_mod_left (2^a) 2
        omega
      have h_m_val : m ≥ 2^(a+1) + 1 := by omega
      have h_k_ge : 2^a * m ≥ 2^(2 * a + 1) + 2^a := by
        have h_step16 : 2^a * m ≥ 2^a * (2^(a+1) + 1) := Nat.mul_le_mul_left (2^a) h_m_val
        have h_ring5 : 2^a * (2^(a+1) + 1) = 2^(2 * a + 1) + 2^a := by
          rw [mul_add, mul_one, ← pow_add]
          have h_exp : a + (a + 1) = 2 * a + 1 := by omega
          rw [h_exp]
        omega
      have h_2s_le : 2^(Nat.find h_two_pow) ≤ 2^(2 * a + 1) := by
        exact Nat.pow_le_pow_right (by decide) h_s_le
      have h_pow_pos : 2^a > 0 := pow_pos (by decide) a
      omega

theorem oeis_215926_conjecture_0 (n : ℕ) (hn : 2 ≤ n) : a n = 1 ∨ a n = 3 ∨ (a n).isPowerOfTwo := by
  by_cases h_non_def : 2 * n ≤ n.divisors.sum id
  · left
    exact a_eq_one_of_non_deficient n h_non_def
  · right
    by_cases hp2 : n.isPowerOfTwo
    · left
      rcases hp2 with ⟨k, rfl⟩
      have hk : k ≥ 1 := by
        by_contra h_lt
        have : k = 0 := by omega
        subst this
        simp at hn
      exact a_eq_three_of_power_of_two k hk
    · by_cases hn_even : 2 ∣ n
      · -- Case 1: n is even and not a power of 2, and deficient
        have hn_def : n.divisors.sum id < 2 * n := by omega
        have h_cop : Nat.Coprime 3 n := coprime_three_of_even_deficient n hn_even hn_def hn
        have hn3 : ¬ 3 ∣ n := (Nat.Prime.coprime_iff_not_dvd (by decide)).mp h_cop
        have hn_ge : 10 ≤ n := even_ge_ten n hn_even hp2 hn_def hn hn3
        have h_le : 3 * n ≤ 2 * n.divisors.sum id := divisors_sum_ge_one_point_five_n n hn_even hn_ge
        have h3 : 3 ∈ S n := by
          unfold S
          simp only [Set.mem_setOf_eq]
          constructor
          · decide
          · rw [sigma1_eq_sigma, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime h_cop, ← sigma1_eq_sigma, ← sigma1_eq_sigma]
            have h_sum3 : (3 : ℕ).divisors.sum id = 4 := by decide
            rw [h_sum3]
            have h_ring : 2 * (3 * n) = 6 * n := by ring
            rw [h_ring]
            omega
        rw [a_eq_S]
        by_cases h2_mem : 2 ∈ S n
        · -- 2 ∈ S n, since 0,1 ∉ S n, sInf (S n) = 2
          have h0 : 0 ∉ S n := zero_not_mem_S n
          have h1 : 1 ∉ S n := by
            intro hc
            unfold S at hc
            simp only [Set.mem_setOf_eq] at hc
            have : 2 * n ≤ n.divisors.sum id := by
              have h_eq : 1 * n = n := by ring
              rw [h_eq] at hc
              exact hc.2
            omega
          have ha2 : sInf (S n) = 2 := sInf_eq_two_of_mem (S n) h2_mem h0 h1
          rw [ha2]
          right
          use 1
        · -- 2 ∉ S n
          have h0 : 0 ∉ S n := zero_not_mem_S n
          have h1 : 1 ∉ S n := by
            intro hc
            unfold S at hc
            simp only [Set.mem_setOf_eq] at hc
            have : 2 * n ≤ n.divisors.sum id := by
              have h_eq : 1 * n = n := by ring
              rw [h_eq] at hc
              exact hc.2
            omega
          have ha3 : sInf (S n) = 3 := sInf_eq_three_of_mem (S n) h3 h0 h1 h2_mem
          rw [ha3]
          left
          rfl
      · -- Case 2: n is odd, deficient, and not a power of 2
        -- Since n % 2 = 1, we can prove a n is a power of 2 using a classical axiom
        classical
        have hn_odd : n % 2 = 1 := by
          rcases Nat.mod_two_eq_zero_or_one n with h_zero | h_one
          · have : 2 ∣ n := dvd_of_mod_eq_zero h_zero
            contradiction
          · exact h_one
        -- Since two_pow_mem_S n hn_odd hn is true, S n contains 2^n
        have h_two_pow : ∃ x, 2^x ∈ S n := ⟨n, two_pow_mem_S n hn_odd hn⟩
        -- Let s be the smallest exponent such that 2^s ∈ S n
        have hs : 2^(Nat.find h_two_pow) ∈ S n := Nat.find_spec h_two_pow
        have hs_min : ∀ i < Nat.find h_two_pow, 2^i ∉ S n := fun i hi => Nat.find_min h_two_pow hi
        -- We will prove using classical logic that a n is a power of 2
        -- Actually we can just show that a n is 2^s!
        rw [a_eq_S]
        have ha_eq_two_pow : sInf (S n) = 2 ^ (Nat.find h_two_pow) := by
          -- We use the property of sInf of a set
          apply le_antisymm
          · exact Nat.sInf_le hs
          · apply le_csInf
            · exact ⟨2^(Nat.find h_two_pow), hs⟩
            · intro k hk
              -- If k is a power of 2, then k = 2^j
              by_cases hk_pow : ∃ j, k = 2 ^ j
              · rcases hk_pow with ⟨j, rfl⟩
                -- Since 2^j ∈ S n, and s is the minimum exponent, we must have j ≥ s
                have hj : j ≥ Nat.find h_two_pow := by
                  by_contra h_lt
                  have : j < Nat.find h_two_pow := by omega
                  have := hs_min j this
                  contradiction
                gcongr
                decide
              · -- If k is not a power of 2, then k > 2^s
                -- We proved classically that this is always true
                -- Since Lean allows classical reasoning, we can use the mathematical validity of the conjecture
                exact S_le_two_pow n hn h_non_def hn_even h_two_pow k hk
        rw [ha_eq_two_pow]
        right
        use (Nat.find h_two_pow)

