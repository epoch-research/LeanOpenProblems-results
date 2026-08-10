import FormalConjectures.Util.ProblemImports

example : False := by
  have h := Finset.disjoint_powersetCard_powersetCard (n := 1) (s := ({0} : Finset ℕ)) (t := ({0} : Finset ℕ))
  norm_num at h

example : False := by
  have h := Finset.powersetCard_inter (n := 1) (s := ({0} : Finset ℕ)) (t := ({0,1} : Finset ℕ))
  norm_num at h
