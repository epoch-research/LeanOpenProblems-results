import Mathlib

def get_divs_in_range (n start len fuel : ℕ) : List ℕ :=
  match fuel with
  | 0 => []
  | f + 1 =>
    if len == 0 then []
    else if len == 1 then (if n % start == 0 then [start] else [])
    else
      let half := len / 2
      get_divs_in_range n start half f ++ get_divs_in_range n (start + half) (len - half) f

def a_tree (n : ℕ) : ℕ :=
  let divs := get_divs_in_range n 1 n (n + 1)
  let s := (divs.zip divs.tail).map (fun p : ℕ × ℕ => p.fst * p.snd) |>.sum
  if s == 0 then 0 else n ^ 2 / s

set_option maxHeartbeats 0

theorem test_eval : a_tree 10000 = 1 := by decide
