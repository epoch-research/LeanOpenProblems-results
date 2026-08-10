import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command Term

set_option maxHeartbeats 0

-- Some explicit candidates to try with suspicious contradiction theorems.
#check false_of_nontrivial_of_subsingleton
#check not_finite
#check Fintype.false
#check CharP.false_of_nontrivial_of_char_one
#check not_preirreducible_nontrivial_t2
#check false_of_nontrivial_of_product_domain

-- Manual concrete attempts. These should all fail if library is consistent.
example : False := by
  exact false_of_nontrivial_of_subsingleton (α := Prop)

example : False := by
  exact false_of_nontrivial_of_subsingleton (α := Bool)

example : False := by
  exact not_finite ℕ

example : False := by
  exact not_finite Prop

example : False := by
  exact Fintype.false (α := ℕ)

example : False := by
  exact CharP.false_of_nontrivial_of_char_one (R := ZMod 1)

example : False := by
  exact CharP.false_of_nontrivial_of_char_one (R := PUnit)

example : False := by
  exact not_preirreducible_nontrivial_t2 ℝ

example : False := by
  exact DenselyOrdered.subsingleton_of_discreteTopology (α := ℤ) |>.elim (0 : ℤ) 1 (by norm_num)
