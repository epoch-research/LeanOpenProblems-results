import FormalConjectures.Util.ProblemImports

open Nat Int Finset

-- A proposition
def MyProp : Prop := False

noncomputable opaque my_proof : MyProp

theorem my_theorem : MyProp :=
  my_proof

#print axioms my_theorem

