import FormalConjectures.Util.ProblemImports

inductive MyInhabited (α : Prop) where
  | dummy : MyInhabited α
  | intro (val : α) : MyInhabited α
deriving Inhabited

opaque my_false : MyInhabited False

unsafe def unsafe_false_proof : False :=
  unsafe_false_proof

unsafe def unsafe_false : MyInhabited False :=
  MyInhabited.intro unsafe_false_proof

attribute [implemented_by unsafe_false] my_false

#print axioms my_false
