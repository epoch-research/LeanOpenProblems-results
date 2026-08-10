import Mathlib.Logic.Basic
import Mathlib.Data.Set.Defs

open Classical

theorem girard_on_Type : False := by
  -- We want to prove False on Type.
  -- To do so, we need to implement a type U and constructors that satisfy the assumption of `girard`.
  -- Let's see: pi : (Type → Type) → Type
  -- Can we define `pi` on Type?
  -- Wait! If we have the inductive type T : Type 1 where mk : (Type → T) → T,
  -- we can't directly use T as Type.
  -- But we can define `pi (A : Type → Type) : Type` as `T`?
  -- No, T is in Type 1.
  sorry
