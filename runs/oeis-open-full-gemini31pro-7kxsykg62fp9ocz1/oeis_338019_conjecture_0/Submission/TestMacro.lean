import Mathlib

theorem foo (n : ℕ) : n = n := rfl

#check (type_of% @foo)
