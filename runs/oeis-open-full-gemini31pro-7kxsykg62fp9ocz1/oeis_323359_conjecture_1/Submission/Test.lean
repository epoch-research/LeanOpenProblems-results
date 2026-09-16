import Submission.Spec
import Mathlib.Data.Nat.Prime.Basic

def is_prime_test (n : ℕ) : Bool :=
  if n < 2 then false
  else
    let rec loop (i : ℕ) :=
      if i * i > n then true
      else if n % i == 0 then false
      else loop (i + 1)
    loop 2

def find_counterexample (n : ℕ) : ℕ :=
  Id.run do
    for i in [1:n+1] do
      let ai := a i
      if ai ≠ 1 ∧ ¬ is_prime_test ai then
        return i
    return 0

#eval! find_counterexample 200
