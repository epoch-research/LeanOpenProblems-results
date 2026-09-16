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

def check_eq (n : ℕ) : Bool :=
  if n = 0 then true
  else
    let S := Nat.sqrt ((n + 1) ^ 3)
    let g := Nat.gcd S (b n)
    a n == S / g

#eval check_eq 1
#eval check_eq 2
#eval check_eq 10
#eval check_eq 100
