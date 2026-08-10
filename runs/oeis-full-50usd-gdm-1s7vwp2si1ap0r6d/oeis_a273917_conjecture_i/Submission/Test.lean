import Mathlib

inductive Bad : Prop where
  | mk : Bool → Bad

theorem test : true = false := by
  have eq : Bad.mk true = Bad.mk false := Subsingleton.elim _ _
  injection eq
