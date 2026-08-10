import FormalConjectures.Util.ProblemImports

open Nat

def A216265 (n : ℕ) : ℕ := Nat.primeCounting (n ^ 3) - Nat.primeCounting (n ^ 3 - n)

theorem oeis_216265_conjecture_0 (n : ℕ) (h : n > 13) : A216265 n > 0 := by
  sorry

#check oeis_216265_conjecture_0
example : (¬ (∀ (n : ℕ), n > 13 → A216265 n > 0)) = (¬ (∀ (n : ℕ), n > 13 → A216265 n > 0)) := rfl
