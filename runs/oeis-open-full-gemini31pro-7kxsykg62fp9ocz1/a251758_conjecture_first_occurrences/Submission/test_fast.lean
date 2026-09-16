import Mathlib

def get_divisors_aux (n d fuel : ℕ) (acc1 acc2 : List ℕ) : List ℕ :=
  match fuel with
  | 0 => acc1.reverse ++ acc2
  | f + 1 =>
    if d * d > n then acc1.reverse ++ acc2
    else if d * d = n then acc1.reverse ++ (d :: acc2)
    else if n % d = 0 then get_divisors_aux n (d + 1) f (d :: acc1) ((n / d) :: acc2)
    else get_divisors_aux n (d + 1) f acc1 acc2

def get_divisors (n : ℕ) : List ℕ :=
  get_divisors_aux n 1 (n + 1) [] []

def a_comp (n : ℕ) : ℕ :=
  let divs := get_divisors n
  let s := (divs.zip divs.tail).map (fun p : ℕ × ℕ => p.fst * p.snd) |>.sum
  if s = 0 then 0 else n ^ 2 / s

def check_range (k : ℕ) (start : ℕ) (len : ℕ) (fuel : ℕ) : Bool :=
  match fuel with
  | 0 => true
  | f + 1 =>
    match len with
    | 0 => true
    | 1 => a_comp start != k
    | _ =>
      let half := len / 2
      check_range k start half f && check_range k (start + half) (len - half) f

#eval check_range 14 2 100000 100
