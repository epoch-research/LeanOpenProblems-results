import Submission.Spec
open Nat Finset

partial def isPrimeComp (n : ℕ) : Bool :=
  if n < 2 then false
  else
    let rec check (k : ℕ) : Bool :=
      if k * k > n then true
      else if n % k == 0 then false
      else check (k + 1)
    check 2

partial def nthPrimeComp (n : ℕ) : ℕ :=
  let rec find (k count : ℕ) : ℕ :=
    if isPrimeComp k then
      if count == n then k
      else find (k + 1) (count + 1)
    else find (k + 1) count
  find 2 0

partial def check_conj (n : ℕ) : Bool :=
  if n = 0 then true else
  let p_n := nthPrimeComp (n - 1)
  let c1 := ((List.range (p_n + 1)).filter (fun p => isPrimeComp p ∧ p % 8 == 1)).length
  let c3 := ((List.range (p_n + 1)).filter (fun p => isPrimeComp p ∧ p % 8 == 3)).length
  let c5 := ((List.range (p_n + 1)).filter (fun p => isPrimeComp p ∧ p % 8 == 5)).length
  let c7 := ((List.range (p_n + 1)).filter (fun p => isPrimeComp p ∧ p % 8 == 7)).length
  let a := (c3 : ℤ) - (c7 : ℤ)
  let b := (c5 : ℤ) - (c1 : ℤ)
  not (a == 0 && b < 0)

partial def find_counterexample : ℕ :=
  let rec loop (n : ℕ) : ℕ :=
    if n > 1000 then 0
    else if not (check_conj n) then n
    else loop (n + 1)
  loop 1

#eval! find_counterexample
