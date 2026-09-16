import Mathlib

def divisors_list_comp (n : ℕ) (k : ℕ) (fuel : ℕ) : List ℕ :=
  match fuel with
  | 0 => []
  | f + 1 =>
    if k > n then []
    else if n % k == 0 then k :: divisors_list_comp n (k + 1) f
    else divisors_list_comp n (k + 1) f

def my_divisors (n : ℕ) : List ℕ := divisors_list_comp n 1 n

#eval my_divisors 12
