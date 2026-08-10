import FormalConjectures.Util.ProblemImports

#check Finset.Coprime_pair_iff
#check Set.HasDensity.univ
#check IsAsymptoticAddBasisOfOrder.of_finite
#check not_isAsymptoticAddBasisOfOrder_zero

example : False := by
  have h := Finset.Coprime_pair_iff ({2} : Finset ℕ) 2 2 (by simp)
  -- Should reduce to Coprime 2 2 ↔ True perhaps false?
  norm_num at h

