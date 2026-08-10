import FormalConjectures.Util.ProblemImports
open Nat

def has_sqrt_aux (fuel : ℕ) (n : ℕ) (k : ℕ) : Bool :=
  match fuel with
  | 0 => false
  | fuel + 1 =>
    if k * k > n then false
    else if k * k == n then true
    else has_sqrt_aux fuel n (k + 1)

def is_square_fast (n : ℕ) : Bool :=
  has_sqrt_aux (n + 1) n 0

theorem not_triangular_6_rfl : is_square_fast (8 * factorial 6 + 1) = false := by decide
theorem not_triangular_10_rfl : is_square_fast (8 * factorial 10 + 1) = false := by decide
