import FormalConjectures.Util.ProblemImports

open Nat

def is_subset_sum : List ℕ → ℕ → Bool
  | [], 0 => true
  | [], _ => false
  | x :: xs, t =>
    if x > t then is_subset_sum xs t
    else is_subset_sum xs (t - x) || is_subset_sum xs t

def remove_one_1 : List ℕ → List ℕ
  | [] => []
  | x :: xs => if x = 1 then xs else x :: remove_one_1 xs

partial def search (c : List ℕ) (current_sum : ℕ) : Bool :=
  let m := c.length
  if m = 19 then
    if current_sum = 1079 then
      is_subset_sum (remove_one_1 c) 57
    else false
  else
    let rem_len := 19 - m
    let min_val := c.headD 1
    
    let max_val1 := if current_sum < 1023 then current_sum + 1 else 1079
    let max_val2 := (1079 - current_sum) / rem_len
    
    let max_val := min max_val1 max_val2
    
    let max_val := if m ≤ 11 then min max_val 127 else max_val
    let max_val := if m ≤ 15 then min max_val 255 else max_val
    let max_val := if m ≤ 17 then min max_val 511 else max_val
    
    let rec loop (x : ℕ) : Bool :=
      if x < min_val then false
      else
        search (x :: c) (current_sum + x) || loop (x - 1)
        
    loop max_val

#eval search [] 0
