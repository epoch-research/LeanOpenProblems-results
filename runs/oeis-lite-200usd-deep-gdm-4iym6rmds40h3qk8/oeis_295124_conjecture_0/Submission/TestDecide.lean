import FormalConjectures.Util.ProblemImports

open Nat Finset

def is_sqfree_computable (n : ℕ) : Bool :=
  decide (Squarefree n)

def count_divisors (n : ℕ) : ℕ :=
  (Nat.divisors n).card

def verify_candidate (a : ℕ) : Bool :=
  (a % 2 != 0) && (a % 3 != 1) && (a % 5 != 2) && (a % 5 != 3) && (a % 7 != 3) && (a % 7 != 5) && (a % 11 != 5) && (a % 11 != 9) && (a % 13 != 6) && (a % 13 != 11) &&
  is_sqfree_computable a && (count_divisors a == 32)

def check_range : ℕ → ℕ → ℕ → Bool
  | _, _, 0 => false
  | a, b, f + 1 =>
    if b < a then true
    else if a = b then
      !verify_candidate a
    else
      let mid := a + (b - a) / 2
      check_range a mid f && check_range (mid + 1) b f

#eval check_range 19636 23204 15
#eval check_range 23206 24000 12

