import Mathlib

open Nat

lemma coprime_of (n T K A p : ℕ) (h2 : n ∣ T^p) (hA : A = 1 + T * K) : Coprime n A := by
  apply Nat.coprime_of_dvd
  intro q hq hqn hqA
  have hqT : q ∣ T := Nat.Prime.dvd_of_dvd_pow hq (Nat.dvd_trans hqn h2)
  have hqTK : q ∣ T * K := dvd_mul_of_dvd_left hqT K
  have hq1 : q ∣ 1 := by
    rw [hA, add_comm] at hqA
    exact (Nat.dvd_add_right hqTK).mp hqA
  exact Nat.Prime.not_dvd_one hq hq1

lemma my_divisibility (n p T A : ℕ) (h1 : n ∣ p * T * A + T^p) (h2 : n ∣ T^p) (hA : ∃ K, A = 1 + T * K) :
  n ∣ p * T := by
  rw [add_comm] at h1
  have h1' : n ∣ p * T * A := (Nat.dvd_add_right h2).mp h1
  rcases hA with ⟨K, hA⟩
  have hcop : Coprime n A := coprime_of n T K A p h2 hA
  exact hcop.dvd_of_dvd_mul_right h1'
