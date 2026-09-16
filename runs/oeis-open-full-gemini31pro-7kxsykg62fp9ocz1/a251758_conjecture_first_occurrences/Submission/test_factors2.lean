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

#eval get_divs [(2, 2), (3, 1)]
