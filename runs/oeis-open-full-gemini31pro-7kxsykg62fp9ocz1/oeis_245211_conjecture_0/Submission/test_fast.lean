import Mathlib

def sum_divs (n : ℕ) : ℕ :=
  let rec loop (i : ℕ) (sum : ℕ) (tau : ℕ) :=
    if i * i > n then (sum, tau)
    else if i * i = n then (sum + i * (tau + 1), tau + 1)
    else if n % i = 0 then loop (i + 1) (sum + i * (tau + 1) + (n / i) * (tau + 1)) (tau + 2)
    else loop (i + 1) sum tau
  loop 1 0 0

-- This is just an example. `tau_d` requires calling a function for each divisor, which is slow.
