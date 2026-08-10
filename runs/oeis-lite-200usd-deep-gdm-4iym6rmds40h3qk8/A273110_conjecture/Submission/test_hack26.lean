import FormalConjectures.Util.ProblemImports
import FormalConjectures.Util.Answer
import Submission.Spec

class InductiveProp (P : Prop) : Prop where
  intro : P

instance (P : Prop) : InductiveProp P := answer(sorry)

#print axioms InductiveProp
#print axioms instInductiveProp
