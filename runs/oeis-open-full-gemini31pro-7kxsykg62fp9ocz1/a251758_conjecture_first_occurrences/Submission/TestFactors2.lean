import Mathlib

def gen_divs (factors : List (ℕ × ℕ)) : List ℕ :=
  match factors with
  | [] => [1]
  | (p, k) :: rest =>
    let divs_rest := gen_divs rest
    let rec mul_powers (fuel : ℕ) (m : ℕ) (pw : ℕ) (acc : List ℕ) : List ℕ :=
      match fuel with
      | 0 => acc
      | f + 1 =>
        match m with
        | 0 => acc
        | c + 1 => mul_powers f c (pw * p) (acc ++ divs_rest.map (fun d => d * pw))
    mul_powers 100 (k + 1) 1 []

def insert_sorted (x : ℕ) : List ℕ → List ℕ
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insert_sorted x ys

def sort_list : List ℕ → List ℕ
  | [] => []
  | x :: xs => insert_sorted x (sort_list xs)

def a_from_factors (n : ℕ) (factors : List (ℕ × ℕ)) : ℕ :=
  let divs := sort_list (gen_divs factors)
  let s := (divs.zip divs.tail).map (fun p : ℕ × ℕ => p.fst * p.snd) |>.sum
  if s == 0 then 0 else n ^ 2 / s

def run_many (len fuel : ℕ) : ℕ :=
  match fuel with
  | 0 => 0
  | f + 1 =>
    if len == 0 then 0
    else if len == 1 then
      if a_from_factors 83521 [(17, 4)] == 14 then 1 else 0
    else
      let half := len / 2
      run_many half f + run_many (len - half) f

set_option maxHeartbeats 0
set_option maxRecDepth 10000000

theorem t : run_many 100000 200000 = 0 := by decide
