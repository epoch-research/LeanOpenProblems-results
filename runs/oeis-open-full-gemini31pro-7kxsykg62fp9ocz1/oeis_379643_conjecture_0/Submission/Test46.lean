import Submission.Spec
open Nat Finset

def isPrimeComp (n : ℕ) : Bool :=
  if n < 2 then false
  else if n == 2 then true
  else (List.range n).drop 2 |>.all (fun m => n % m != 0)

partial def nextPrime (n : ℕ) : ℕ :=
  if isPrimeComp (n + 1) then n + 1 else nextPrime (n + 1)

partial def nthPrimeComp (n : ℕ) : ℕ :=
  let rec loop (k p : ℕ) : ℕ :=
    if k == n then p else loop (k + 1) (nextPrime p)
  loop 0 2

partial def a_comp (n : ℕ) : ℤ :=
  if n == 0 then 0 else
  let p_n := nthPrimeComp (n - 1)
  let count (b : ℕ) := ((List.range (p_n + 1)).filter (fun p => isPrimeComp p ∧ p % 8 == b)).length
  (count 3 : ℤ) - (count 7 : ℤ)

partial def b_comp (n : ℕ) : ℤ :=
  if n == 0 then 0 else
  let p_n := nthPrimeComp (n - 1)
  let count (b : ℕ) := ((List.range (p_n + 1)).filter (fun p => isPrimeComp p ∧ p % 8 == b)).length
  (count 5 : ℤ) - (count 1 : ℤ)

#eval! (List.range 50).map (fun n => (n, a_comp n, b_comp n))
