import FormalConjectures.Util.ProblemImports
open Nat Int Finset

def f (k : ℕ) : ℤ := ((-1 : ℤ)^k) * ((factorial 1194648 : ℤ) / (k : ℤ))

def K : ℤ := (factorial 1194648 : ℤ) / (factorial 1093 : ℤ)

lemma f_m (m : ℕ) (hm : m ∈ Icc 1 1092) :
  f (m * 1093) = K * (((-1 : ℤ)^m) * ((factorial 1092 : ℤ) / (m : ℤ))) := by
  dsimp [f, K]
  -- We know (-1)^(m * 1093) = (-1)^m
  have h_sign : (-1 : ℤ)^(m * 1093) = (-1 : ℤ)^m := by
    have : m * 1093 = m * 1092 + m := by ring
    rw [this, pow_add, pow_mul]
    have h_even : (-1 : ℤ)^1092 = 1 := by decide
    rw [h_even, one_pow, one_mul]
  rw [h_sign]
  sorry
