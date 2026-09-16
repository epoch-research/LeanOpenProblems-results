import Mathlib

def loop (n : Nat) (acc : Nat) : Nat :=
  match n with
  | 0 => acc
  | k + 1 => loop k (acc + 1)

set_option maxRecDepth 2000000000

theorem test : loop 4000000 0 = 4000000 := by decide
