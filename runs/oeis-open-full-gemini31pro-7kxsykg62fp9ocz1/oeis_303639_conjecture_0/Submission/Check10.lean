import Mathlib

def my_sqrt_loop (n : Nat) : Nat → Nat
| 0 => 0
| g + 1 => if (g + 1) * (g + 1) ≤ n then g + 1 else my_sqrt_loop n g

def my_sqrt (n : Nat) : Nat := my_sqrt_loop n n

theorem test1 : my_sqrt 10 = 3 := by decide
