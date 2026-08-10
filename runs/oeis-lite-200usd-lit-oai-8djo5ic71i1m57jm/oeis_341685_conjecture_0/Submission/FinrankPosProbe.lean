import FormalConjectures.Util.ProblemImports
#check Module.finrank_pos
#check finrank_pos
#check Module.finrank_pos_iff
#check Module.finrank_eq_zero
example : 0 < Module.finrank ℚ (Padic 3) := by
  exact Module.finrank_pos
