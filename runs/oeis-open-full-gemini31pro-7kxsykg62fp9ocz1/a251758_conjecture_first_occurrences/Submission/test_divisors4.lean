import Mathlib

def div_loop (n d : ℕ) (low high : List ℕ) (fuel : ℕ) : List ℕ × List ℕ :=
  match fuel with
  | 0 => (low, high)
  | f + 1 =>
    if h : d * d > n then (low, high)
    else if n % d == 0 then
      if d * d == n then (low ++ [d], high)
      else div_loop n (d + 1) (low ++ [d]) ((n / d) :: high) f
    else div_loop n (d + 1) low high f

def fast_divisors (n : ℕ) : List ℕ :=
  let (low, high) := div_loop n 1 [] [] (n + 1)
  low ++ high

#eval fast_divisors 12
