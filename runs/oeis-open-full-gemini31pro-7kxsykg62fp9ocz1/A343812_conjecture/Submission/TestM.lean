import Mathlib

open Nat Finset

def primes : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29,
   31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
   73, 79, 83, 89, 97, 101, 103, 107, 109, 113]

def p (i : ℕ) : ℕ := primes.getD i 0
def S (n : ℕ) : ℕ := (range n).sum p
def a_comp (n : ℕ) : ℕ := (range n).sum (fun i => S n % p i)

def a_vals := (List.range 30).map (fun i => a_comp i)
#eval a_vals
