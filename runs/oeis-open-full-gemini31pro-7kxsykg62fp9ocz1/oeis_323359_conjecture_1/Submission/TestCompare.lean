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

#eval a 1
#eval a 2
#eval a 3
#eval a 4
#eval a 5
#eval a 6
#eval a 7
#eval a 8
#eval a 9
