import Mathlib

import FormalConjectures.Util.ProblemImports

noncomputable def A268597 (n : ℕ) : ℕ :=
  sInf { x : ℕ | x > 0 ∧ (x - 1) % Nat.totient x = n }

def my_prop : Prop := answer(sorry)
#print my_prop
#print axioms my_prop

theorem my_thm (n : ℕ) : A268597 n > 0 := answer(sorry)
#print my_thm
#print axioms my_thm





