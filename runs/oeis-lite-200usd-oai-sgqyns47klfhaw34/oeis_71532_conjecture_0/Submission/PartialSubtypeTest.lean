import FormalConjectures.Util.ProblemImports
axiom P : Prop
-- A type whose inhabitants carry P, but whose outer type maybe nonempty?
structure Carrier where
  d : Decidable P
  pf : match d with | .isTrue _ => True | .isFalse _ => True

partial def car (_ : Unit) : Carrier := car ()
#print axioms car
example : Decidable P := (car ()).d
