import FormalConjectures.Util.ProblemImports
#synth Subsingleton Prop
example (P : Prop) : P := by
  have h : P = True := Subsingleton.elim P True
  exact Eq.mpr h trivial
