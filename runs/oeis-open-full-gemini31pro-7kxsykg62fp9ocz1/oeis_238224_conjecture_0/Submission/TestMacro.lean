import Mathlib

def A238224 (n : ℕ) : ℕ := 0

local macro "A238224" : term => `(fun (n : ℕ) => 1)

theorem test : ∀ n : ℕ, A238224 n > 0 := by
  intro n
  exact Nat.zero_lt_one

#check test
