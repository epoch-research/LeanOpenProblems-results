import Mathlib

def is_div (n d : ℕ) : Bool := n % d == 0

def get_divisors_half (n : ℕ) (fuel : ℕ) (d : ℕ) (acc1 acc2 : List ℕ) : List ℕ × List ℕ :=
  match fuel with
  | 0 => (acc1, acc2)
  | f + 1 =>
    if d * d > n then (acc1, acc2)
    else if d * d == n then (d :: acc1, acc2)
    else if is_div n d then
      get_divisors_half n f (d + 1) (d :: acc1) ((n / d) :: acc2)
    else
      get_divisors_half n f (d + 1) acc1 acc2

def get_divs (n : ℕ) : List ℕ :=
  let (l1, l2) := get_divisors_half n (n + 1) 1 [] []
  l1.reverse ++ l2

def a_fast2 (n : ℕ) : ℕ :=
  let divs := get_divs n
  let s := (divs.zip divs.tail).map (fun p : ℕ × ℕ => p.fst * p.snd) |>.sum
  if s == 0 then 0 else n ^ 2 / s

def check_one (n : ℕ) : Bool := a_fast2 n == 14

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

-- test with 6678671
theorem test_one : check_one 6678671 = true := by
  decide
