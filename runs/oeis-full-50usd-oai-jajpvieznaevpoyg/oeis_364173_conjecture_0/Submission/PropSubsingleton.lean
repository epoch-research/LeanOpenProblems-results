import FormalConjectures.Util.ProblemImports
#synth Subsingleton Prop
example (P : Prop) : True = P := by exact?
example (P : Prop) : P := by
  have hprop : Prop := answer(sorry)
  -- hprop is True
  fail_if_success have heq : hprop = P := by exact Subsingleton.elim _ _
  sorry
