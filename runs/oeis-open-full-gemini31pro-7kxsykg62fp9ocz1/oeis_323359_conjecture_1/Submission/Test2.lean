import Submission.Spec
import Mathlib.Data.Nat.Prime.Basic

def is_prime_test : ℕ → Bool
| 0 => false
| 1 => false
| 2 => true
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

#eval! find_counterexample 100
