import Submission.Spec
open Nat

def is_prime_test (n : ℕ) : Bool :=
  if n < 2 then false
  else if n = 2 then true
  else if n % 2 = 0 then false
  else
    let rec loop (i : ℕ) : Bool :=
      if i * i > n then true
      else if n % i = 0 then false
      else loop (i + 2)
    loop 3

def check_all (start : ℕ) (stop : ℕ) : IO Unit := do
  for n in [start:stop] do
    let val := a n
    if val != 1 && !is_prime_test val then
      IO.println s!"Counterexample found at n = {n}, a(n) = {val}"

#eval check_all 3 1000
