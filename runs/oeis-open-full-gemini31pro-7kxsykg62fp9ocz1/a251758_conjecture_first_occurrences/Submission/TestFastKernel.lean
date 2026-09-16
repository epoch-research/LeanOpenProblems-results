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

def get_divs (n : ℕ) : List ℕ :=
  if n % 2 == 0 then []
  else
    let (l1, l2) := get_divs_odd n 1 (n/2 + 2) [] []
    l1.reverse ++ l2

def a_fast_opt (n : ℕ) : ℕ :=
  let divs := get_divs n
  let s := (divs.zip divs.tail).map (fun p : ℕ × ℕ => p.fst * p.snd) |>.sum
  if s == 0 then 0 else n ^ 2 / s

def check_n (n : ℕ) : Bool :=
  if n % 2 == 0 then true
  else if n % 3 == 0 then true
  else if n % 5 == 0 then true
  else if n % 7 == 0 then true
  else if n % 11 == 0 then true
  else if n % 13 == 0 then true
  else a_fast_opt n != 14

def check_range (start len fuel : ℕ) : Bool :=
  match fuel with
  | 0 => true
  | f + 1 =>
    if len == 0 then true
    else if len == 1 then check_n start
    else
      let half := len / 2
      check_range start half f && check_range (start + half) (len - half) f

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

-- test with 10,000 numbers in a range with large numbers
