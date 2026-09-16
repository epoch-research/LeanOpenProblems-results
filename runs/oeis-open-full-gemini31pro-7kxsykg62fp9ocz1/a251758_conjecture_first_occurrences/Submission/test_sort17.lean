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

def a_fast (n : ℕ) : ℕ :=
  let divs := fast_divisors n
  let s := (divs.zip divs.tail).map (fun p => p.1 * p.2) |>.sum
  if s = 0 then 0 else n ^ 2 / s

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
set_option maxRecDepth 1000000
theorem t1 : check_range 6600000 10000 20 = true := by decide
