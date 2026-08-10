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

lemma coprime_eight_of_odd {k : ℕ} (h : k % 2 = 1) : (8 : ℕ).Coprime k := by
  rw [Nat.Coprime, Nat.gcd_comm]
  have h_dvd : Nat.gcd k 8 ∣ 8 := Nat.gcd_dvd_right k 8
  have h_cases : Nat.gcd k 8 ∈ [1, 2, 4, 8] := by
    -- 8 = 2^3, its only divisors are 1, 2, 4, 8
    sorry
  sorry
