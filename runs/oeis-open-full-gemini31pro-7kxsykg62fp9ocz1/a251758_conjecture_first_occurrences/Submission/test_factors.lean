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

#eval generate_divisors [(2, 2), (3, 1)]
