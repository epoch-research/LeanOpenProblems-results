import FormalConjectures.Util.ProblemImports

example (h0 : ∃ z : ℤ, z = 0) (h1 : ∃ z : ℤ, z = 1) :
    HEq h0 h1 := proof_irrel_heq h0 h1

example (h0 : ∃ z : ℤ, z = 0) (h1 : ∃ z : ℤ, z = 1) :
    Classical.choose h0 = Classical.choose h1 := by
  have hh : HEq h0 h1 := proof_irrel_heq h0 h1
  -- try subst? cases?
  -- cases hh
  fail_if_success cases hh
  fail_if_success exact heq_iff_eq.mp (congr_heq (f := Classical.choose) hh)
  sorry
