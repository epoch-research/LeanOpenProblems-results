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

partial def a_comp (n : ℕ) : ℤ :=
  if n = 0 then 0 else
  let p_n := nthPrimeComp (n - 1)
  let c3 := ((List.range (p_n + 1)).filter (fun p => isPrimeComp p ∧ p % 8 == 3)).length
  let c7 := ((List.range (p_n + 1)).filter (fun p => isPrimeComp p ∧ p % 8 == 7)).length
  (c3 : ℤ) - (c7 : ℤ)

partial def b_comp (n : ℕ) : ℤ :=
  if n = 0 then 0 else
  let p_n := nthPrimeComp (n - 1)
  let c5 := ((List.range (p_n + 1)).filter (fun p => isPrimeComp p ∧ p % 8 == 5)).length
  let c1 := ((List.range (p_n + 1)).filter (fun p => isPrimeComp p ∧ p % 8 == 1)).length
  (c5 : ℤ) - (c1 : ℤ)

#eval a_comp 1
#eval b_comp 1
#eval a_comp 4
#eval b_comp 4
#eval a_comp 11
#eval b_comp 11
