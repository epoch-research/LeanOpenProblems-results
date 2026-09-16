import Mathlib
open List Finset

def check_divs (n : ℕ) (l : List ℕ) : Bool :=
  l.head? == some 1 && l.getLast? == some n &&
  l.Pairwise (· < ·) &&
  l.all (fun d => n % d == 0) &&
  -- How to check NO OTHER divisors exist?
  true
