import FormalConjectures.Util.ProblemImports
open Nat

def b : ℕ → ℕ
| 0 => 0
| 1 => 2
| k_plus_1 + 1 =>
  let k := k_plus_1 + 1
  let b_prev := b k_plus_1
  b_prev + Nat.lcm (Nat.sqrt (k ^ 3)) b_prev

def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    (b (n + 1) / b n) - 1

def check_all : ℕ → ℕ
| 0 => 0
| n + 1 =>
  let an := a (n + 1)
  if an != 1 && !an.Prime then
    n + 1
  else
    check_all n

#eval check_all 2000
