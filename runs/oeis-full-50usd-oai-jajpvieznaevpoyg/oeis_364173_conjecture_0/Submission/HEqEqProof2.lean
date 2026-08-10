import FormalConjectures.Util.ProblemImports

theorem zero_eq_one_via_heq : (0:ℤ) = 1 := by
  have h : HEq (show (0:ℤ)=0 from rfl) (show (1:ℤ)=1 from rfl) := proof_irrel_heq _ _
  exact nomatch h

#print axioms zero_eq_one_via_heq
