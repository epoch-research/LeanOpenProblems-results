import FormalConjectures.Util.ProblemImports
partial def loopFun {P : Prop} (u : Unit) : P := loopFun u
example : False := loopFun ()
#print axioms loopFun
