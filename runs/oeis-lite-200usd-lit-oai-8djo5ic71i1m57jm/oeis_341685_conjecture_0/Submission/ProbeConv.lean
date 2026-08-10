import FormalConjectures.Util.ProblemImports

open AdditiveCombinatorics

example : sumRep (∅ : Set ℕ) 0 = 0 := by native_decide
example : sumRep ({0} : Set ℕ) 0 = 1 := by native_decide
example : sumRep ({0,1} : Set ℕ) 1 = 2 := by native_decide

example : False := by
  have h := sumRep_eq_powerSeries_coeff ({0} : Set ℕ) 0
  norm_num [sumRep, sumConv] at h
