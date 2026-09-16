import Mathlib

def check_div_tree (n start len fuel : ℕ) : List ℕ :=
  match fuel with
  | 0 => []
  | f + 1 =>
    if len == 0 then []
    else if len == 1 then
      if start > 0 && n % start == 0 then [start] else []
    else
      let half := len / 2
      check_div_tree n start half f ++ check_div_tree n (start + half) (len - half) f

set_option maxHeartbeats 0
set_option maxRecDepth 10000000

theorem t1 : (check_div_tree 6678671 0 6678672 30).length = 32 := by decide
