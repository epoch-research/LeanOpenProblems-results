import Mathlib

def div_loop (n d : ℕ) (fuel : ℕ) : List ℕ :=
  match fuel with
  | 0 => []
  | f + 1 =>
    if h : d * d > n then []
    else if d * d == n then [d]
    else if n % d == 0 then d :: (div_loop n (d + 1) f) ++ [n / d]
    else div_loop n (d + 1) f

def fast_divisors (n : ℕ) : List ℕ :=
  div_loop n 1 (n + 1)

#eval fast_divisors 12
