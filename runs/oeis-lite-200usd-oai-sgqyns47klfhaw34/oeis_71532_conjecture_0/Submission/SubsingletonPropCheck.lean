import FormalConjectures.Util.ProblemImports
#synth Subsingleton Prop
#check subsingleton_of_forall_eq
example (P : Prop) : P := by
  have e : P = True := Subsingleton.elim P True
  exact of_eq_true e
