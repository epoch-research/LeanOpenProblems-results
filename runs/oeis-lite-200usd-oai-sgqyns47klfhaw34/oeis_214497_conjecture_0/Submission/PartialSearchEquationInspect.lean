import FormalConjectures.Util.ProblemImports

partial def fsearch (n : ℕ) : ℕ := if n = 0 then 0 else fsearch (n-1)
#print fsearch
#check fsearch.eq_1
#print axioms fsearch

example : fsearch 0 = 0 := by
  simp [fsearch]

example : fsearch 2 = 0 := by
  simp [fsearch]
