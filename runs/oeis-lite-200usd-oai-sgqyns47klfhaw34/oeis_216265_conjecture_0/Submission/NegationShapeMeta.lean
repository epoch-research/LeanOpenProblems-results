import FormalConjectures.Util.ProblemImports
open Nat

def A216265 (n : ℕ) : ℕ := Nat.primeCounting (n ^ 3) - Nat.primeCounting (n ^ 3 - n)

theorem oeis_216265_conjecture_0 (n : ℕ) (h : n > 13) : A216265 n > 0 := by
  sorry

#check (show (¬ (∀ (n : ℕ), n > 13 → A216265 n > 0)) from by
  intro H
  have h14 : A216265 14 > 0 := H 14 (by norm_num)
  -- This is the expected shape; no way to use n=13.
  guard_target = False
  sorry)
#print oeis_216265_conjecture_0
