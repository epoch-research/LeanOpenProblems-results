import FormalConjectures.Util.ProblemImports

set_option maxHeartbeats 0
set_option maxRecDepth 200000

def totient_fast_loop (n : Nat) : Nat → Nat → Nat
  | 0, acc => acc
  | i + 1, acc =>
    if (i + 1).Coprime n then
      totient_fast_loop n i (acc + 1)
    else
      totient_fast_loop n i acc

def totient_fast (n : Nat) : Nat :=
  if n = 0 then 0
  else totient_fast_loop n (n - 1) 0

theorem test_tail : totient_fast 100000 = 40000 := by decide
