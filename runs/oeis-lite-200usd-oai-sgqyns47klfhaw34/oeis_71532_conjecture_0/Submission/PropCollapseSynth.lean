import FormalConjectures.Util.ProblemImports
#synth Subsingleton Prop
#synth Unique Prop
example (P : Prop) : P := by
  have hEq : P = True := Subsingleton.elim P True
  exact Eq.mpr hEq.symm True.intro
