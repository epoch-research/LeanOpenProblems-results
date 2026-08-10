import FormalConjectures.Util.ProblemImports

open Relation

-- Try relation by target proposition
example (P : Prop) : Relation.EqvGen (fun A B : Prop => B) True P := by
  apply Relation.EqvGen.symm
  apply Relation.EqvGen.rel
  trivial

-- Can endpoint be extracted? (expected no; symm blocks it)
example (P : Prop) (h : Relation.EqvGen (fun A B : Prop => B) True P) : P := by
  induction h with
  | refl => trivial
  | rel hrel => exact hrel
  | symm _ ih => sorry
  | trans _ _ ih1 ih2 => exact ih2

-- Try relation allowing only forward from True to P, tagged by source True.
-- If EqvGen introduces symmetry, extraction likely impossible.
example (P : Prop) : Quot.mk (fun A B : Prop => A = True) True = Quot.mk _ P := Quot.sound rfl

#check Quot.eq
