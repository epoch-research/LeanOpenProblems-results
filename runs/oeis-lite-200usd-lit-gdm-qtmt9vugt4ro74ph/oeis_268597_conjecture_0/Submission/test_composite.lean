import Mathlib

open Nat

lemma composite_factorization (C : ℕ) (hC : C ≥ 2) (hp : ¬ C.Prime) :
  ∃ m d, m ≥ 2 ∧ d ≥ 2 ∧ C = m * d := by
  have h_not_one : C ≠ 1 := by omega
  obtain ⟨p, hp_prime, hp_div⟩ := Nat.exists_prime_and_dvd h_not_one
  obtain ⟨d, hd_eq⟩ := hp_div
  refine ⟨p, d, hp_prime.two_le, ?_, hd_eq⟩
  by_contra h_lt
  have hd_lt_two : d < 2 := by omega
  interval_cases d
  · rw [hd_eq] at hC
    omega
  · rw [hd_eq] at hp
    rw [mul_one] at hp
    exact hp hp_prime
