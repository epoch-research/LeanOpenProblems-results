import Mathlib

def generate_divisors (factors : List (ℕ × ℕ)) : List ℕ :=
  match factors with
  | [] => [1]
  | (p, k) :: rest =>
    let sub := generate_divisors rest
    let rec build (power : ℕ) (c : ℕ) : List ℕ :=
      match c with
      | 0 => sub.map (· * power)
      | c' + 1 => sub.map (· * power) ++ build (power * p) c'
    build 1 k

def get_divs (factors : List (ℕ × ℕ)) : List ℕ :=
  let divs := generate_divisors factors
  divs.insertionSort (· ≤ ·)

def a_from_factors (n : ℕ) (factors : List (ℕ × ℕ)) : ℕ :=
  let divs := get_divs factors
  let s := (divs.zip divs.tail).map (fun p => p.1 * p.2) |>.sum
  if s = 0 then 0 else n ^ 2 / s

#eval a_from_factors 12 [(2, 2), (3, 1)]
