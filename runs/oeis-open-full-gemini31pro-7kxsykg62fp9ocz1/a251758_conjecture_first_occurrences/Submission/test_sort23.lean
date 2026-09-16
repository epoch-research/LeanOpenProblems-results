import Mathlib

def my_divs_loop (n d fuel : ℕ) (low high : List ℕ) : List ℕ :=
  match fuel with
  | 0 => low ++ high
  | f + 1 =>
    if d * d > n then low ++ high
    else if n % d == 0 then
      if d * d == n then low ++ [d] ++ high
      else my_divs_loop n (d + 1) f (low ++ [d]) ((n / d) :: high)
    else my_divs_loop n (d + 1) f low high

def fast_divs (n : ℕ) : List ℕ := my_divs_loop n 1 (n + 1) [] []

theorem fast_divs_eq (n : ℕ) : fast_divs n = (Nat.divisors n).sort (· ≤ ·) := by sorry
