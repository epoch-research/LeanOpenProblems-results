import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open Nat

def totient_fast_loop (n : Nat) : Nat → Nat → Nat
  | 0, acc => acc
  | i + 1, acc =>
    if (i + 1).Coprime n then
      totient_fast_loop n i (acc + 1)
    else
      totient_fast_loop n i acc

def totient_fast (n : Nat) : Nat :=
  if n = 0 then 0
  else if n = 1 then 1
  else totient_fast_loop n (n - 1) 0

theorem test_speed : totient_fast 10000 = 4000 := by decide
