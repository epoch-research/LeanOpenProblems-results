import FormalConjectures.Util.ProblemImports

open Nat Finset

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

theorem test_coprime_4 (n : ℕ) (hn : n % 2 = 1) : Nat.Coprime 4 n := by
  have h2 := test_coprime_2 n hn
  -- Let's try to prove Coprime 4 n using Coprime 2 n
  have h_coprime : Nat.Coprime (2^2) n := Nat.Coprime.pow_left 2 h2
  exact h_coprime

theorem test_coprime_8 (n : ℕ) (hn : n % 2 = 1) : Nat.Coprime 8 n := by
  have h2 := test_coprime_2 n hn
  have h_coprime : Nat.Coprime (2^3) n := Nat.Coprime.pow_left 3 h2
  exact h_coprime

theorem sigma1_eq_sigma (m : ℕ) : m.divisors.sum id = ArithmeticFunction.sigma 1 m := by
  rw [ArithmeticFunction.sigma_one_apply]
  rfl

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
  -- n is even and not a power of 2 and not divisible by 3.
  -- since n >= 2, we can just do case analysis using omega
  rcases hn_even with ⟨m, rfl⟩
  -- n = 2 * m
  -- if m = 1, then n = 2, which is 2^1, contradiction
  -- if m = 2, then n = 4, which is 2^2, contradiction
  -- if m = 3, then n = 6, but 3 ∣ 6, contradiction
  -- if m = 4, then n = 8, which is 2^3, contradiction
  -- so m ≥ 5, so n ≥ 10
  have hm : m ≥ 5 := by
    by_contra h_lt
    have : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl
    · omega
    · -- n = 2 = 2^1
      have hc : ∃ k, 2 = 2^k := ⟨1, by rfl⟩
      exact h_not hc
    · -- n = 4 = 2^2
      have hc : ∃ k, 4 = 2^k := ⟨2, by rfl⟩
      exact h_not hc
    · -- n = 6, 3 ∣ 6
      have hc : 3 ∣ 6 := ⟨2, by rfl⟩
      exact hn3 hc
    · -- n = 8 = 2^3
      have hc : ∃ k, 8 = 2^k := ⟨3, by rfl⟩
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
  -- they are distinct
  have hab : n ≠ n / 2 := by omega
  have hac : n ≠ 2 := by omega
  have had : n ≠ 1 := by omega
  have hbc : n / 2 ≠ 2 := by omega
  have hbd : n / 2 ≠ 1 := by omega
  have hcd : 2 ≠ 1 := by omega
  have h_sum := divisors_sum_ge_four_divisors n n (n/2) 2 1 hd1 hd2 hd3 hd4 hab hac had hbc hbd hcd
  -- sum is n + n/2 + 2 + 1
  -- we want 3 * n <= 2 * sum
  have h_div : n = (n / 2) * 2 := by
    rw [Nat.div_mul_cancel hn_even]
  omega






theorem odd_ge_three (n : ℕ) (hn : n % 2 = 1) (hn2 : 2 ≤ n) : 3 ≤ n := by
  omega

theorem minFac_dvd_of_odd (n : ℕ) (hn : n % 2 = 1) (hn2 : 2 ≤ n) : minFac n ∣ n := minFac_dvd n

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


def S (n : ℕ) : Set ℕ :=
  {k : ℕ | k.divisors.sum id < 2 * k ∧ 2 * (k * n) ≤ (k * n).divisors.sum id}

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
  · -- 2^n is deficient
    rw [divisors_sum_two_pow]
    have h_pos : 2 ^ (n + 1) > 0 := pow_pos (by decide) (n + 1)
    have h_eq : 2 * 2 ^ n = 2 ^ (n + 1) := by ring
    rw [h_eq]
    omega
  · -- 2^n * n is non-deficient
    have h_coprime := test_coprime_pow n hn n
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










