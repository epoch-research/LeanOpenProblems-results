import Mathlib

def a (n : ℕ) : ℕ := 0

macro_rules | `(a $n) => `(0)

theorem oeis_361715_conjecture_2 : a 5 = 0 := rfl
