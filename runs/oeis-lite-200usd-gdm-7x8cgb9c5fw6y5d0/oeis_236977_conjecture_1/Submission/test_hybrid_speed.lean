import FormalConjectures.Util.ProblemImports

set_option maxHeartbeats 0
set_option maxRecDepth 200000

open Nat Finset

def totient_leaf_loop (n : Nat) : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | fuel + 1, L, R =>
    if L > R then 0
    else
      let count := if L.Coprime n then 1 else 0
      count + totient_leaf_loop n fuel (L + 1) R

def totient_range (n : Nat) : Nat → Nat → Nat → Nat
  | 0, L, R => totient_leaf_loop n 2050 L R
  | fuel + 1, L, R =>
    if L > R then 0
    else if L = R then
      if L.Coprime n then 1 else 0
    else
      let mid := (L + R) / 2
      totient_range n fuel L mid + totient_range n fuel (mid + 1) R

def totient_fast (n : Nat) : Nat :=
  if n = 0 then 0
  else if n = 1 then 1
  else totient_range n 10 1 (n - 1)

theorem test_eval_large : totient_fast 100000 = 40000 := by decide
