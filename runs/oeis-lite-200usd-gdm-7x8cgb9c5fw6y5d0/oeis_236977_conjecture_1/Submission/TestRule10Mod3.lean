import FormalConjectures.Util.ProblemImports

open Nat

lemma Nat.sqrt_sq (x : ℕ) : sqrt (x ^ 2) = x := by
  have h1 : x * x ≤ x * x := le_rfl
  have h2 : x ≤ sqrt (x * x) := le_sqrt.mpr h1
  have h3 : sqrt (x * x) * sqrt (x * x) ≤ x * x := sqrt_le (x * x)
  have h4 : sqrt (x * x) ≤ x := by
    nlinarith
  have h5 : sqrt (x * x) = x := le_antisymm h4 h2
  rw [show x ^ 2 = x * x by ring]
  exact h5

lemma coprime_two_of_odd {k : ℕ} (h : k % 2 = 1) : (2 : ℕ).Coprime k := by
  rw [Nat.Coprime, Nat.gcd_comm]
  have h_dvd : Nat.gcd k 2 ∣ 2 := Nat.gcd_dvd_right k 2
  have h_cases : Nat.gcd k 2 = 1 ∨ Nat.gcd k 2 = 2 := by
    have h_prime : Nat.Prime 2 := Nat.prime_two
    rcases (Nat.dvd_prime h_prime).mp h_dvd with h1 | h2
    · left; exact h1
    · right; exact h2
  rcases h_cases with h_gcd1 | h_gcd2
  · exact h_gcd1
  · have h_dvd_left : Nat.gcd k 2 ∣ k := Nat.gcd_dvd_left k 2
    rw [h_gcd2] at h_dvd_left
    have h_mod0 : k % 2 = 0 := Nat.mod_eq_zero_of_dvd h_dvd_left
    omega

theorem rule_10_mod (n : ℕ) (h_mod : n % 10 = 0) (h_gt : n ≥ 10) :
    ∃ k ∈ Finset.Ico 1 ((n - 1) / 2 + 1), sqrt (totient k * totient (n - k)) ^ 2 = totient k * totient (n - k) := by
  let m := n / 10
  have h_n : n = 10 * m := by omega
  have h_m_gt : m ≥ 1 := by omega
  let k := 2 * m
  use k
  have h_gt_k : k ≥ 1 := by omega
  have h_lt_k : k < (n - 1) / 2 + 1 := by omega
  have h_mem : k ∈ Finset.Ico 1 ((n - 1) / 2 + 1) := Finset.mem_Ico.mpr ⟨h_gt_k, h_lt_k⟩
  refine ⟨h_mem, ?_⟩
  have h_sub : n - k = 8 * m := by omega
  rw [h_sub]
  by_cases h_even : 2 ∣ m
  · -- Case 1: 2 ∣ m
    have h_tot_2m : totient (2 * m) = 2 * totient m :=
      totient_mul_of_prime_of_dvd Nat.prime_two h_even
    have h_dvd_2m : 2 ∣ 2 * m := by omega
    have h_tot_4m : totient (4 * m) = 4 * totient m := by
      have h_eq : 4 * m = 2 * (2 * m) := by ring
      rw [h_eq, totient_mul_of_prime_of_dvd Nat.prime_two h_dvd_2m, h_tot_2m]
      ring
    have h_dvd_4m : 2 ∣ 4 * m := by omega
    have h_tot_8m : totient (8 * m) = 8 * totient m := by
      have h_eq : 8 * m = 2 * (4 * m) := by ring
      rw [h_eq, totient_mul_of_prime_of_dvd Nat.prime_two h_dvd_4m, h_tot_4m]
      ring
    rw [h_tot_2m, h_tot_8m]
    have h_prod : 2 * totient m * (8 * totient m) = (4 * totient m) ^ 2 := by ring
    rw [h_prod, Nat.sqrt_sq]
  · -- Case 2: ¬ 2 ∣ m (m is odd)
    have h_odd : m % 2 = 1 := by omega
    have h_cop_2 : (2 : ℕ).Coprime m := coprime_two_of_odd h_odd
    have h_cop_8 : (8 : ℕ).Coprime m := by
      have h_eq : (8 : ℕ) = 2 ^ 3 := by rfl
      rw [h_eq]
      exact h_cop_2.pow_left 3
    rw [totient_mul h_cop_2, totient_mul h_cop_8]
    have h_tot2 : totient 2 = 1 := rfl
    have h_tot8 : totient 8 = 4 := rfl
    rw [h_tot2, h_tot8]
    have h_prod : 1 * totient m * (4 * totient m) = (2 * totient m) ^ 2 := by ring
    rw [h_prod, Nat.sqrt_sq]
