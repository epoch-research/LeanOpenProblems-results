import FormalConjectures.Util.ProblemImports
open Nat

-- What is Nat.nth Nat.Prime at small indices?
example : Nat.nth Nat.Prime 0 = 2 := by
  have := Nat.nth_count (p := Nat.Prime) (n := 2) (by norm_num)
  simp at this
  sorry

-- check via known lemma names
open Nat in
#check @Nat.nth_prime_eq  -- maybe doesn't exist
