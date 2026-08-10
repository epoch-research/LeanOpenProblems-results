import FormalConjectures.Util.ProblemImports

#synth Subsingleton Prop
#synth Unique Prop
#synth Subsingleton (Type)
#synth Nontrivial Prop

example : False := by
  have h : (True : Prop) = False := Subsingleton.elim True False
  simpa using congrArg (fun P : Prop => P) h
