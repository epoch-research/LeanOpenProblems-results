import FormalConjectures.Util.ProblemImports
#synth Subsingleton Prop
example (P : Prop) : P := by
  have hEq : P = True := Subsingleton.elim P True
  exact Eq.mp hEq True.intro
