import FormalConjectures.Util.ProblemImports

inductive BadIdx2 : Prop → Type
| intro : BadIdx2 True
  deriving Nonempty

#check instNonemptyBadIdx2
#print instNonemptyBadIdx2
#print axioms instNonemptyBadIdx2
