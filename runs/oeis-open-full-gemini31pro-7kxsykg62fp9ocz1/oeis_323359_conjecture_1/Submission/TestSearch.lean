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

def check_range (start len : ℕ) : ℕ :=
  match len with
  | 0 => 0
  | len' + 1 =>
    let n := start + len'
    let an := a n
    if n > 0 && an != 1 && !an.Prime then
      n
    else
      check_range start len'

#eval check_range 1 2000
