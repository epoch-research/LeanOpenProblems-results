import Mathlib

def list_divs (n x fuel : ℕ) : List ℕ :=
  match fuel with
  | 0 => []
  | f + 1 =>
    if x > n then []
    else if n % x == 0 then x :: list_divs n (x + 1) f
    else list_divs n (x + 1) f

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem t1 : list_divs 6678671 1 10000 = [1] := by decide
