import FormalConjectures.Util.ProblemImports
partial def loopProp (P : Prop) [Inhabited P] : P := loopProp P
-- can't inhabit arbitrary P
-- unsafe axiom-like?
#print axioms loopProp
