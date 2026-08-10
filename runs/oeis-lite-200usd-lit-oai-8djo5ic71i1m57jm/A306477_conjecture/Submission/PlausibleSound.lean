import FormalConjectures.Util.ProblemImports

example : 1 + 1 = 2 := by plausible
#print axioms PlausibleSound._example_1

-- should fail if sound
example : False := by plausible
#print axioms PlausibleSound._example_2
