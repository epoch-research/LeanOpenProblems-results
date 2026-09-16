import Mathlib
open List Finset

def list_divisors (n : ℕ) : List ℕ :=
  (List.range (n + 1)).filter (fun x => if h : x > 0 then n % x == 0 else false)

def a_comp (n : ℕ) : ℕ :=
  let divs := list_divisors n
  let s := (divs.zip divs.tail).map (fun p => p.1 * p.2) |>.sum
  if s = 0 then 0 else n ^ 2 / s

#eval a_comp 667867
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem t1 : a_comp 50000 = 12500 := by decide
