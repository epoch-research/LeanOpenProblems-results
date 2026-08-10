import FormalConjectures.Util.ProblemImports
theorem tt2 : (2^10 / 2^3) % 2^4 = 0 := by decide +kernel
#print axioms tt2
#eval IO.println "REACHED-END"
