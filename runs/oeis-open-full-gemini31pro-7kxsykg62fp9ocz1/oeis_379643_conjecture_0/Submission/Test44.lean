import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Defs

def isPrimeFast (n : ℕ) : Bool :=
  if n < 2 then false
  else if n == 2 then true
  else if n % 2 == 0 then false
  else
    let rec check (k : ℕ) : Bool :=
      if k * k > n then true
      else if n % k == 0 then false
      else check (k + 2)
    check 3
  termination_by n - 3

def nthPrime (n : ℕ) : ℕ :=
  let rec loop (k : ℕ) (p : ℕ) : ℕ :=
    if k == n then p
    else
      let rec nextPrime (m : ℕ) : ℕ :=
        if isPrimeFast m then m else nextPrime (m + 1)
      loop (k + 1) (nextPrime (p + 1))
  loop 0 2

def a_eval (n : ℕ) : ℤ :=
  if n == 0 then 0 else
  let p_n := nthPrime (n - 1)
  let count (b : ℕ) := ((List.range (p_n + 1)).filter (fun p => isPrimeFast p ∧ p % 8 == b)).length
  (count 3 : ℤ) - (count 7 : ℤ)

def b_eval (n : ℕ) : ℤ :=
  if n == 0 then 0 else
  let p_n := nthPrime (n - 1)
  let count (b : ℕ) := ((List.range (p_n + 1)).filter (fun p => isPrimeFast p ∧ p % 8 == b)).length
  (count 5 : ℤ) - (count 1 : ℤ)

def check_n (n : ℕ) : Bool :=
  a_eval n == 0 && b_eval n < 0

#eval (List.range 1000).filter check_n
