import Mathlib

inductive MyProp : Prop where
  | mk : (False → MyProp) → MyProp

mutual
  partial def get_myProp (u : Unit) : MyProp :=
    get_myProp u

  partial def get_myProp_helper (u : Unit) : Nonempty MyProp :=
    ⟨get_myProp u⟩
end















