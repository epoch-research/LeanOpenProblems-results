import FormalConjectures.Util.ProblemImports

partial def badSearch (k : Nat) : Nat :=
  if False then k else badSearch (k+1)

#print badSearch
#print axioms badSearch
#check badSearch.eq_def

example : False := by
  let k := badSearch 0
  -- Can we exploit the equation?
  have h := badSearch.eq_def 0
  simp [badSearch] at h
  -- h : badSearch 0 = badSearch 1
  guard_hyp h : badSearch 0 = badSearch 1
  sorry
