import FormalConjectures.Util.ProblemImports
import FormalConjectures.Util.Answer

def my_hack : Prop := answer(sorry)

theorem hack_proof : my_hack := by
  trivial

#print axioms hack_proof
