import Mathlib

def a_fast_loop (n d fuel : ℕ) (last_d : ℕ) (sum_lower sum_upper : ℕ) : ℕ × ℕ :=
  match fuel with
  | 0 => (sum_lower, sum_upper)
  | f + 1 =>
    if d * d > n then
      (sum_lower + last_d * (n / last_d), sum_upper)
    else if n % d == 0 then
      if d * d == n then
        (sum_lower + last_d * d, sum_upper + d * (n / last_d))
      else
        a_fast_loop n (d + 2) f d (sum_lower + last_d * d) (sum_upper + (n / d) * (n / last_d))
    else
      a_fast_loop n (d + 2) f last_d sum_lower sum_upper

def a_fast4 (n : ℕ) : ℕ :=
  let (s1, s2) := a_fast_loop n 3 (n/2+2) 1 0 0
  let s := s1 + s2
  if s == 0 then 0 else n ^ 2 / s

set_option maxHeartbeats 0
set_option maxRecDepth 10000000

theorem t_check : a_fast4 6678671 = 14 := by decide
