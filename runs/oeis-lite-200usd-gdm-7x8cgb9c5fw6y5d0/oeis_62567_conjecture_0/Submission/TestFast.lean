import FormalConjectures.Util.ProblemImports

open Nat

def digits_fast_helper : ℕ → ℕ → List ℕ
  | 0, _ => []
  | fuel + 1, n =>
    if n = 0 then []
    else (n % 10) :: digits_fast_helper fuel (n / 10)

def digits_fast (n : ℕ) : List ℕ :=
  digits_fast_helper n n

def reverse_nat_fast (n : ℕ) : ℕ :=
  ofDigits 10 (digits_fast n).reverse

-- Let's see if we can prove reverse_nat_fast 9 = 9 by decide!
theorem rev_nine_fast : reverse_nat_fast 9 = 9 := by decide
