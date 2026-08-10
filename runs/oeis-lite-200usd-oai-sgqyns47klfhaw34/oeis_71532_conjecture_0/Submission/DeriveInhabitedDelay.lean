import FormalConjectures.Util.ProblemImports
inductive Delay where
| later : Delay -> Delay
  deriving Inhabited, Nonempty
#check (default : Delay)
#print axioms Delay.instInhabited
#print axioms Delay.instNonempty
