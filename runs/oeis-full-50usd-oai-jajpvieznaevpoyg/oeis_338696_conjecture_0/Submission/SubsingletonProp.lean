import FormalConjectures.Util.ProblemImports
#synth Subsingleton Prop
example (p : Prop) : p = True := Subsingleton.elim p True
