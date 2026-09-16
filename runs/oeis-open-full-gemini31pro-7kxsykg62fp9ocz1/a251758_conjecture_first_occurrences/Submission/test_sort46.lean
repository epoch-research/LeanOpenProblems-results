import Mathlib

def list_divs_loop (n d fuel : ℕ) (low high : List ℕ) : List ℕ :=
  match fuel with
  | 0 => low ++ high
  | f + 1 =>
    if d * d > n then low ++ high
    else if n % d == 0 then
      if d * d == n then low ++ [d] ++ high
      else list_divs_loop n (d + 1) f (low ++ [d]) ((n / d) :: high)
    else list_divs_loop n (d + 1) f low high

def fast_divs (n : ℕ) : List ℕ := list_divs_loop n 1 (n + 1) [] []

def a_fast (n : ℕ) : ℕ :=
  let divs := fast_divs n
  let s := (divs.zip divs.tail).map (fun p => p.1 * p.2) |>.sum
  if s = 0 then 0 else n ^ 2 / s

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem t1 : a_fast 6678671 = 14 := by decide
