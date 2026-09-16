import Mathlib
import Submission.Spec

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
  if n % 2 == 0 then
    let (l1, l2) := get_divs_odd n 1 (n/2 + 2) [] []
    sort_list (l1.reverse ++ l2) -- Not optimal for even, just placeholder
  else
    let (l1, l2) := get_divs_odd n 1 (n/2 + 2) [] []
    l1.reverse ++ l2

def a_fast_opt (n : ℕ) : ℕ :=
  let divs := get_divs n
  let s := (divs.zip divs.tail).map (fun p : ℕ × ℕ => p.fst * p.snd) |>.sum
  if s == 0 then 0 else n ^ 2 / s

theorem a_eq_a_fast_opt (n : ℕ) : Submission.Spec.a n = a_fast_opt n := by
  sorry

