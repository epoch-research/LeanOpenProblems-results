import FormalConjectures.Util.ProblemImports
#synth Nontrivial Prop
#synth Subsingleton Prop

def QAll := Quot (fun _ _ : Bool => True)
#synth Subsingleton QAll
#synth Nontrivial QAll
example : False := by
  exact false_of_nontrivial_of_subsingleton QAll
