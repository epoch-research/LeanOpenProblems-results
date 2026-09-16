import Mathlib

def get_divisors (n : ℕ) : List ℕ :=
  (List.range (n + 1)).filter (fun d => d > 0 ∧ n % d = 0)

def a_comp (n : ℕ) : ℕ :=
  let divs := get_divisors n
  let s := (divs.zip divs.tail).map (fun p : ℕ × ℕ => p.fst * p.snd) |>.sum
  if s = 0 then 0 else n ^ 2 / s

theorem test_a2 : a_comp 4 = 1 := by decide
