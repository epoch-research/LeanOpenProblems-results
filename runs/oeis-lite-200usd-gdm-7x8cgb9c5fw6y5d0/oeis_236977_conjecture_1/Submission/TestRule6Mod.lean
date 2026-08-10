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

theorem rule_6_mod (n : ℕ) (h_mod : n % 6 = 0) (h_not_mod : n % 30 ≠ 0) (h_gt : n ≥ 9) :
    ∃ k ∈ Finset.Ico 1 ((n - 1) / 2 + 1), sqrt (totient k * totient (n - k)) ^ 2 = totient k * totient (n - k) := by
  let m := n / 6
  have h_n : n = 6 * m := by omega
  have h_m_gt : m ≥ 2 := by omega
  have h_cop : (5 : ℕ).Coprime m := by
    rw [Nat.Coprime]
    have h_dvd : Nat.gcd 5 m ∣ 5 := Nat.gcd_dvd_left 5 m
    have h_cases : Nat.gcd 5 m = 1 ∨ Nat.gcd 5 m = 5 := by
      have h_prime : Nat.Prime 5 := by decide
      rcases (Nat.dvd_prime h_prime).mp h_dvd with h1 | h2
      · left; exact h1
      · right; exact h2
    rcases h_cases with h_gcd1 | h_gcd5
    · exact h_gcd1
    · -- if gcd = 5, then 5 ∣ m, so 30 ∣ 6*m = n, contradiction
      have h_dvd_m : Nat.gcd 5 m ∣ m := Nat.gcd_dvd_right 5 m
      rw [h_gcd5] at h_dvd_m
      have h_30 : 30 ∣ n := by
        rw [h_n]
        rcases h_dvd_m with ⟨c, hc⟩
        use c
        rw [hc]
        ring
      have h_mod30 : n % 30 = 0 := Nat.mod_eq_zero_of_dvd h_30
      omega
  let k := m
  use k
  have h_gt_k : k ≥ 1 := by omega
  have h_lt_k : k < (n - 1) / 2 + 1 := by omega
  have h_mem : k ∈ Finset.Ico 1 ((n - 1) / 2 + 1) := Finset.mem_Ico.mpr ⟨h_gt_k, h_lt_k⟩
  refine ⟨h_mem, ?_⟩
  have h_sub : n - k = 5 * m := by omega
  rw [h_sub]
  rw [totient_mul h_cop]
  have h_tot5 : totient 5 = 4 := rfl
  rw [h_tot5]
  have h_prod : totient m * (4 * totient m) = (2 * totient m) ^ 2 := by ring
  rw [h_prod, Nat.sqrt_sq]
