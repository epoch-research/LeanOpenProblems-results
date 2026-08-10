import Mathlib

structure Wrap (α : Type) : Type where
  f : α → False

inductive MyType : Type where
  | mk : Wrap MyType → MyType
