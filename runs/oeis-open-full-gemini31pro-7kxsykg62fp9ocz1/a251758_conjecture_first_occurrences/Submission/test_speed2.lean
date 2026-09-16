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

def a_fast (n : ℕ) : ℕ :=
  if n % 2 == 0 then 1 else
  if n % 3 == 0 then 2 else
  if n % 5 == 0 then 4 else
  if n % 7 == 0 then 6 else
  let (s1, s2) := a_fast_loop n 11 3000 1 0 0
  let s := s1 + s2
  if s == 0 then 0 else n ^ 2 / s

def check_range (start len fuel : ℕ) : Bool :=
  match fuel with
  | 0 => true
  | f + 1 =>
    if len == 0 then true
    else if len == 1 then a_fast start != 14
    else
      let half := len / 2
      check_range start half f && check_range (start + half) (len - half) f

set_option maxHeartbeats 0
set_option maxRecDepth 10000000

theorem t1 : check_range 17 5000 20 = true := by decide
