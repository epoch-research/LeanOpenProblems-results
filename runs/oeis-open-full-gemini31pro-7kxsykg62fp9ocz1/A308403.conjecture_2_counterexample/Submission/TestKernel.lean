import Mathlib

def loop (n : Nat) (acc : Nat) : Nat :=
  match n with
  | 0 => acc
  | k + 1 => loop k (acc + 1)

theorem test : loop 1000000 0 = 1000000 := by decide
