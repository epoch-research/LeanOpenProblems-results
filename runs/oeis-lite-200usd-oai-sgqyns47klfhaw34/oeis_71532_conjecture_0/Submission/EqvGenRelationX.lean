import FormalConjectures.Util.ProblemImports

open Relation

def R (X Y : Prop) : Prop := X

theorem eqv_true_right {P : Prop} : EqvGen R True P := EqvGen.rel _ _ True.intro

-- Try prove endpoint from EqvGen R True P
theorem endpoint {P : Prop} : EqvGen R True P -> P := by
  intro h
  induction h with
  | rel x y hx =>
      -- x=True? because start True? induction generalized loses endpoints?
      dsimp [R] at hx
      -- goal y? maybe
      assumption
  | refl x =>
      -- goal x? if x=True? 
      trivial
  | symm x y h ih =>
      -- from Eqv y x and ih? let's see
      exact ?_
  | trans x y z h1 h2 ih1 ih2 => exact ih2

example (P:Prop) : P := endpoint (P:=P) eqv_true_right
#print axioms endpoint
#print axioms _example
