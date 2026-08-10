import FormalConjectures.Util.ProblemImports

example (P : Prop) (h : P = False) : ¬ P := by
  intro hp
  have hf : False := by simpa [h] using hp
  exact hf

example (P : Prop) (h : P = True) : P := by
  simpa [h]

-- Cannot derive P from P=False branch.
example (P : Prop) (h : P = False) : P := by
  fail_if_success simpa [h]
  fail_if_success exact False.elim (by simpa [h] : False)
  admit
