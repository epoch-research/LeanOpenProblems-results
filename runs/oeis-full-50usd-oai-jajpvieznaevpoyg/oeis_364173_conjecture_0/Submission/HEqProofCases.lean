import FormalConjectures.Util.ProblemImports

example : (0:ℤ) = 1 := by
  have h : HEq (show (0:ℤ)=0 from rfl) (show (1:ℤ)=1 from rfl) := proof_irrel_heq _ _
  cases h
  -- see goal

example : (0:ℤ) = 1 := by
  have h : HEq (show (0:ℤ)=0 from rfl) (show (1:ℤ)=1 from rfl) := proof_irrel_heq _ _
  induction h
