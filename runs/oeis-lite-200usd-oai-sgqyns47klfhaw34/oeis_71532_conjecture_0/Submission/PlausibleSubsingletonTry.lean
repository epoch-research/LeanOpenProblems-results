import FormalConjectures.Util.ProblemImports
#synth Subsingleton (Plausible.TestResult False)
#synth Subsingleton (Plausible.TestResult True)
example : False := by
  have h : (default : Plausible.TestResult False) = Plausible.TestResult.success (PSum.inl ()) := Subsingleton.elim _ _
  cases h
#print axioms _example
