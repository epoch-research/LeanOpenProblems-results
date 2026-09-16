import Mathlib

def div_loop (n d fuel : ℕ) (low high : List ℕ) : List ℕ × List ℕ :=
  match fuel with
  | 0 => (low, high)
  | f + 1 =>
    if h : d * d > n then (low, high)
    else if n % d == 0 then
      if d * d == n then (low ++ [d], high)
      else div_loop n (d + 1) f (low ++ [d]) ((n / d) :: high)
    else div_loop n (d + 1) f low high

def fast_divisors (n : ℕ) : List ℕ :=
  let (low, high) := div_loop n 1 (n + 1) [] []
  low ++ high
