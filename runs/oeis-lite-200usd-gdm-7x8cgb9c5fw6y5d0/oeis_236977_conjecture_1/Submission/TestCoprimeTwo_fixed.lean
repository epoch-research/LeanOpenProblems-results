import FormalConjectures.Util.ProblemImports

open Nat

lemma coprime_two_of_odd {k : ℕ} (h : k % 2 = 1) : (2 : ℕ).Coprime k := by
  rw [Nat.Coprime, Nat.gcd_comm]
  have h_dvd_left : Nat.gcd k 2 ∣ k := Nat.gcd_dvd_left k 2
  have h_dvd_right : Nat.gcd k 2 ∣ 2 := Nat.gcd_dvd_right k 2
  omega
