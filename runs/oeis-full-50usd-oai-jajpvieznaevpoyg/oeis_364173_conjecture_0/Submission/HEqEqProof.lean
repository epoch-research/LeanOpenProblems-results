import FormalConjectures.Util.ProblemImports

example : HEq (show (0:ℤ)=0 from rfl) (show (1:ℤ)=1 from rfl) := proof_irrel_heq _ _

example : (0:ℤ) = 1 := by
  have h : HEq (show (0:ℤ)=0 from rfl) (show (1:ℤ)=1 from rfl) := proof_irrel_heq _ _
  -- try cases
  fail_if_success cases h
  fail_if_success exact nomatch h
  apply?
