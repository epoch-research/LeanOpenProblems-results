import FormalConjectures.Util.ProblemImports
open Nat

def A216265 (n : ℕ) : ℕ := Nat.primeCounting (n ^ 3) - Nat.primeCounting (n ^ 3 - n)

example (n : ℕ) (h : n > 13) : A216265 n > 0 := by
  fail_if_success exact cast (by congr) True.intro
  fail_if_success exact Eq.ndrec True.intro (by congr : True = (A216265 n > 0))
  fail_if_success subst_vars
  fail_if_success congr
  sorry
