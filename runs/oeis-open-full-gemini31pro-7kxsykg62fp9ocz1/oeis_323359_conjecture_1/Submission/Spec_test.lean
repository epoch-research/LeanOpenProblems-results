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
  else (b (n + 1) / b n) - 1

def is_prime_test : ℕ → Bool
| 0 => false
| 1 => false
| n => 
  Id.run <| do
    for i in [2:n] do
      if i * i > n then return true
      if n % i == 0 then return false
    return true

def find_counterexample (n : ℕ) : ℕ :=
  Id.run <| do
    for i in [1:n+1] do
      let ai := a i
      if ai ≠ 1 ∧ ¬ is_prime_test ai then
        return i
    return 0

#eval find_counterexample 200
