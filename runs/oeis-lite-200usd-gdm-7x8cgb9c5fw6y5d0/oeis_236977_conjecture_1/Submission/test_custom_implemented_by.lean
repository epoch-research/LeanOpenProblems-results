import FormalConjectures.Util.ProblemImports

open Nat

def my_slow_function (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | n + 1 => my_slow_function n + 1

def my_fast_function (n : Nat) : Nat := n

attribute [implemented_by my_fast_function] my_slow_function

-- If implemented_by is used by decide, then my_slow_function 10000 = 10000 should prove instantly with no stack overflow!
theorem test_dec : my_slow_function 10000 = 10000 := by
  decide
