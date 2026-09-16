import FormalConjectures.Util.ProblemImports
open Nat Finset

lemma gb_prop2 (m : ℕ) (p : ℕ) (hp_prime : Nat.Prime p) (hp_gt : Nat.sqrt m < p) (hp_le : p ≤ m / 2) :
    m ≥ 6 := by
  by_contra h
  push_neg at h
  have hp2 : p ≥ 2 := hp_prime.two_le
  interval_cases m
  · omega
  · omega
  · omega
  · omega
  · have e1 : Nat.sqrt 4 = 2 := by decide
    have e2 : 4 / 2 = 2 := by decide
    rw [e1] at hp_gt
    rw [e2] at hp_le
    omega
  · have e1 : Nat.sqrt 5 = 2 := by decide
    have e2 : 5 / 2 = 2 := by decide
    rw [e1] at hp_gt
    rw [e2] at hp_le
    omega

