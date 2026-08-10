import FormalConjectures.Util.ProblemImports
open Relation

abbrev r (a b : Prop) : Prop := b

example (P : Prop) (h : EqvGen r P False) : P := by
  induction h with
  | rel x y hy =>
    change x
    cases hy
  | refl x =>
    change x
    -- x is False? no, because target in motive not fixed in induction generalized, goal x for refl x impossible
    sorry
  | symm x y h ih =>
    -- goal?
    sorry
  | trans x y z h1 h2 ih1 ih2 =>
    sorry
