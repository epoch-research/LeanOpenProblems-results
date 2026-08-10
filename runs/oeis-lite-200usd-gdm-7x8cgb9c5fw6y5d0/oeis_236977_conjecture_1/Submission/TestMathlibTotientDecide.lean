import FormalConjectures.Util.ProblemImports

open Nat

def check_one_mathlib (L : Nat) : Bool :=
  -- let's use a dummy witness or look it up
  let k := 1
  let m := totient k * totient (L - k)
  sqrt m ^ 2 == m

#eval totient 1000

theorem test_dec : totient 1000 = 400 := by decide
