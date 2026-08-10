import FormalConjectures.Util.ProblemImports

#reduce (default : Plausible.TestResult False)
#print Plausible.instInhabitedTestResult
#print axioms Plausible.instInhabitedTestResult

example (P : Prop) : Plausible.TestResult P := default
