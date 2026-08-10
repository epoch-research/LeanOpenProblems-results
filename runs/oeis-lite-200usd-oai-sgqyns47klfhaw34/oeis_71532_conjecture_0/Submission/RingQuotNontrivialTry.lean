import FormalConjectures.Util.ProblemImports

def relAll (x y : ℕ) := True
#synth Inhabited (RingQuot relAll)
#synth Nontrivial (RingQuot relAll)
#synth Subsingleton (RingQuot relAll)
example : False := by
  exact false_of_nontrivial_of_subsingleton (RingQuot relAll)
#print axioms _example
