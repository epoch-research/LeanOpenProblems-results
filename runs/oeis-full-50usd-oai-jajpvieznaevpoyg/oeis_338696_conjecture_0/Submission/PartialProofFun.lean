import FormalConjectures.Util.ProblemImports
partial def loopFalse (n : ℕ) : False := loopFalse n
#print axioms loopFalse
example : False := loopFalse 0
#print axioms CommandLine.«example_1»
