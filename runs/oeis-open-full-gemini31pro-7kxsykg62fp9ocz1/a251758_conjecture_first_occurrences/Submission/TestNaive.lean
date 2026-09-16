import Mathlib

def get_divisors_tail (n d fuel : ℕ) (acc : List ℕ) : List ℕ :=
  match fuel with
  | 0 => acc
  | f + 1 =>
    if d == 0 then acc
    else if n % d == 0 then get_divisors_tail n (d - 1) f (d :: acc)
    else get_divisors_tail n (d - 1) f acc

def a_naive (n : ℕ) : ℕ :=
  let divs := get_divisors_tail n n n []
  let s := (divs.zip divs.tail).map (fun p : ℕ × ℕ => p.fst * p.snd) |>.sum
  if s == 0 then 0 else n ^ 2 / s

set_option maxHeartbeats 0
set_option maxRecDepth 10000000

theorem t : a_naive 6678671 = 14 := by decide
