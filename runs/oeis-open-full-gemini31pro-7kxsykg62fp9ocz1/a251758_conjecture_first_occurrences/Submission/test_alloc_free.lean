import Mathlib

def div_sum_small (n d prev_d s fuel : ℕ) : ℕ × ℕ :=
  match fuel with
  | 0 => (prev_d, s)
  | f + 1 =>
    if d * d > n then (prev_d, s)
    else if n % d == 0 then
      div_sum_small n (d + 1) d (s + prev_d * d) f
    else
      div_sum_small n (d + 1) prev_d s f

-- Wait, this doesn't give us the large divisors easily without storing the small ones!
