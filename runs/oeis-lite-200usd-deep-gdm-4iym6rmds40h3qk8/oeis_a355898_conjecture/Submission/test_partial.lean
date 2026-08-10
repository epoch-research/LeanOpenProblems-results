import Mathlib

inductive Box (P : Prop) : Type where
  | mk : P → Box P

partial def get_box (P : Prop) : Box P :=
  get_box P
