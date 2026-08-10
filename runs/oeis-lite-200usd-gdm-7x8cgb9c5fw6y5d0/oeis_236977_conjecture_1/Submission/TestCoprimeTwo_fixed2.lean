import FormalConjectures.Util.ProblemImports

open Nat

lemma coprime_two_of_odd {k : ℕ} (h : k % 2 = 1) : (2 : ℕ).Coprime k := by
  rw [Nat.Coprime, Nat.gcd_comm]
  have h_dvd : Nat.gcd k 2 ∣ 2 := Nat.gcd_dvd_right k 2
  have h_cases : Nat.gcd k 2 = 1 ∨ Nat.gcd k 2 = 2 := by
    -- 2 is prime
    have h_prime : Nat.Prime 2 := Nat.prime_two
    rcases (Nat.dvd_prime h_prime).mp h_dvd with h1 | h2
    · left; exact h1
    · right; exact h2
  rcases h_cases with h_gcd1 | h_gcd2
  · exact h_gcd1
  · -- if Nat.gcd k 2 = 2, then 2 ∣ k, which contradicts k % 2 = 1
    have h_dvd_left : Nat.gcd k 2 ∣ k := Nat.gcd_dvd_left k 2
    rw [h_gcd2] at h_dvd_left
    have h_mod0 : k % 2 = 0 := Nat.mod_eq_zero_of_dvd h_dvd_left
    omega
