import FormalConjectures.Util.ProblemImports
#synth Subsingleton Prop
example : False := by
  have h : True = False := Subsingleton.elim True False
  exact Eq.mp h True.intro
