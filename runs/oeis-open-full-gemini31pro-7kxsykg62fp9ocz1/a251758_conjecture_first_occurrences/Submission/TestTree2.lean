import Mathlib

def get_divs_half_tree (n start len fuel : ℕ) : List ℕ :=
  match fuel with
  | 0 => []
  | f + 1 =>
    if len == 0 then []
    else if len == 1 then
      let d := start
      if d * d > n then []
      else if d * d == n then [d]
      else if n % d == 0 then [d, n / d]
      else []
    else
      let half := len / 2
      get_divs_half_tree n start half f ++ get_divs_half_tree n (start + half) (len - half) f

def insert_sorted (x : ℕ) : List ℕ → List ℕ
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insert_sorted x ys

def sort_list : List ℕ → List ℕ
  | [] => []
  | x :: xs => insert_sorted x (sort_list xs)

def get_divs (n : ℕ) : List ℕ :=
  let unsorted := get_divs_half_tree n 1 3000 3000
  sort_list unsorted

def a_fast3 (n : ℕ) : ℕ :=
  let divs := get_divs n
  let s := (divs.zip divs.tail).map (fun p : ℕ × ℕ => p.fst * p.snd) |>.sum
  if s == 0 then 0 else n ^ 2 / s

set_option maxHeartbeats 0

theorem test_eval : a_fast3 6678671 = 14 := by decide
