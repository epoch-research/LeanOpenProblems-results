import FormalConjectures.Util.ProblemImports
open Nat List Finset

theorem pc (P : Prop) : P ∨ ¬ P := Classical.em P
#print axioms pc
#print axioms Classical.propComplete
#print axioms Classical.choice
#print axioms Nat.find
#print axioms Classical.decEq
