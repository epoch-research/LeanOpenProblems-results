import Mathlib

def count_divs_in_range (n start len fuel : ℕ) : ℕ :=
  match fuel with
  | 0 => 0
  | f + 1 =>
    if len == 0 then 0
    else if len == 1 then
      let d := start
      if d * d > n then 0
      else if d * d == n then 1
      else if n % d == 0 then 2
      else 0
    else
      let half := len / 2
      count_divs_in_range n start half f + count_divs_in_range n (start + half) (len - half) f

set_option maxHeartbeats 0

theorem test_eval : count_divs_in_range 6678671 1 3000 3000 = 32 := by decide
