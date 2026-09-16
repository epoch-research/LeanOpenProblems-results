import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

open Nat Finset

partial def isPrimeFast (n : ℕ) : Bool :=
  if n < 2 then false else
  let rec loop (i : ℕ) : Bool :=
    if i * i > n then true
    else if n % i == 0 then false
    else loop (i + 1)
  loop 2

def A261627_comp (n : ℕ) : ℕ :=
  let n' := if n % 2 == 1 then 1 else 2
  let candidate_primes := (Finset.range (n + 1)).filter (fun p => isPrimeFast p)
  (candidate_primes.filter (fun p =>
    let k := p * n' - 1
    k < n ∧ isPrimeFast (n - k) ∧ isPrimeFast (n + k)
  )).card

def singletons : List ℕ := [5, 7, 10, 11, 12, 19, 22, 30, 34, 44, 46, 72, 142]

def check_conj (n : ℕ) : Bool :=
  let a := A261627_comp n
  let p1 := if n > 6 then a > 0 else true
  let p2 := (a == 1) == (singletons.contains n)
  p1 && p2

#eval! (List.range 1000).all check_conj
