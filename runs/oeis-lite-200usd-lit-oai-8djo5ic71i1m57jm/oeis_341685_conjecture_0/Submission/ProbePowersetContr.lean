import FormalConjectures.Util.ProblemImports

example : False := by
  have h := Finset.powersetCard_inter (n := 1) (s := ({0} : Finset ℕ)) (t := ({1} : Finset ℕ))
  -- LHS empty, RHS { {0} } ∩ { {1} } empty, ok
  simp at h

example : False := by
  have h := Finset.powersetCard_inter (n := 1) (s := ({0,1} : Finset ℕ)) (t := ({1,2} : Finset ℕ))
  simp at h
