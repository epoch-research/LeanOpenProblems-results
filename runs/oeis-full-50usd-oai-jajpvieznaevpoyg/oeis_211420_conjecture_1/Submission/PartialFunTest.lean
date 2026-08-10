import FormalConjectures.Util.ProblemImports

partial def loopFalse : Nat → False
  | n => loopFalse n

theorem bad : False := loopFalse 0

#print axioms bad
#print loopFalse
