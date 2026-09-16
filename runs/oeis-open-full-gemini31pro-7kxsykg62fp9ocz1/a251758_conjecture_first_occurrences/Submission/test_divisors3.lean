import Mathlib

def div_loop (n d : ℕ) (low high : List ℕ) : List ℕ × List ℕ :=
  if h : d * d > n then (low, high)
  else
    have : n - (d + 1) < n - d := by
      apply Nat.sub_succ_lt_self
      omega
    if n % d == 0 then
      if d * d == n then (low ++ [d], high)
      else div_loop n (d + 1) (low ++ [d]) ((n / d) :: high)
    else div_loop n (d + 1) low high
termination_by n - d

def fast_divisors (n : ℕ) : List ℕ :=
  let (low, high) := div_loop n 1 [] []
  low ++ high

#eval fast_divisors 12
