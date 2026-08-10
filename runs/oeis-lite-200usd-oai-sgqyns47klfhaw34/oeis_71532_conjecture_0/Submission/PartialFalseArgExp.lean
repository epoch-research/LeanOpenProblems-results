import FormalConjectures.Util.ProblemImports
partial def loopFalse (_ : Unit) : False := loopFalse ()
#print axioms loopFalse
example : False := loopFalse ()
#print axioms PartialFalseArgExp._example_1
