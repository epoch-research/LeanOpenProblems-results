import Mathlib

def get_divs_odd (n : ℕ) (d : ℕ) (fuel : ℕ) (acc1 acc2 : List ℕ) : List ℕ × List ℕ :=
  match fuel with
  | 0 => (acc1, acc2)
  | f + 1 =>
    if d * d > n then (acc1, acc2)
    else if d * d == n then (d :: acc1, acc2)
    else if n % d == 0 then
      get_divs_odd n (d + 2) f (d :: acc1) ((n / d) :: acc2)
    else
      get_divs_odd n (d + 2) f acc1 acc2

def insert_sorted (x : ℕ) : List ℕ → List ℕ
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insert_sorted x ys

def sort_list : List ℕ → List ℕ
  | [] => []
  | x :: xs => insert_sorted x (sort_list xs)

def get_divs (n : ℕ) : List ℕ :=
  if n % 2 == 0 then []
  else
    let (l1, l2) := get_divs_odd n 3 2500 [1] [n]
    sort_list (l1.reverse ++ l2)

def a_fast_opt (n : ℕ) : ℕ :=
  let divs := get_divs n
  let s := (divs.zip divs.tail).map (fun p : ℕ × ℕ => p.fst * p.snd) |>.sum
  if s == 0 then 0 else n ^ 2 / s

def check_range (start len fuel : ℕ) : ℕ :=
  match fuel with
  | 0 => 0
  | f + 1 =>
    if len == 0 then 0
    else if len == 1 then
      if start % 2 == 0 || start % 3 == 0 || start % 5 == 0 || start % 7 == 0 || start % 11 == 0 || start % 13 == 0 then 0
      else if a_fast_opt start == 14 then 1 else 0
    else
      let half := len / 2
      check_range start half f + check_range (start + half) (len - half) f

set_option maxHeartbeats 0
set_option maxRecDepth 10000000

theorem t_check : check_range 6678600 72 200000 = 1 := by decide
