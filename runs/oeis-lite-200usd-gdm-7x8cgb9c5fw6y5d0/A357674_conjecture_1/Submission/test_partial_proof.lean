import Mathlib

structure Wrap (P : Prop) : Type where
  val : P

partial def get_wrap (P : Prop) [Nonempty (Wrap P)] : Wrap P := get_wrap P

theorem test_false (h : Nonempty (Wrap False)) : False := (get_wrap False).val
