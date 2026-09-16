import Mathlib

def div_loop (n d fuel : ℕ) (acc : List ℕ) : List ℕ :=
  match fuel with
  | 0 => acc.reverse
  | f + 1 =>
    if h : d > n then acc.reverse
    else if n % d == 0 then div_loop n (d + 1) f (d :: acc)
    else div_loop n (d + 1) f acc

def fast_divisors (n : ℕ) : List ℕ := div_loop n 1 (n + 1) []

set_option maxHeartbeats 0
set_option maxRecDepth 10000000
#eval fast_divisors 50000
theorem t1 : fast_divisors 50000 = [1, 2, 4, 5, 8, 10, 16, 20, 25, 40, 50, 80, 100, 125, 200, 250, 400, 500, 625, 1000, 1250, 2000, 2500, 3125, 5000, 6250, 10000, 12500, 25000, 50000] := by decide
