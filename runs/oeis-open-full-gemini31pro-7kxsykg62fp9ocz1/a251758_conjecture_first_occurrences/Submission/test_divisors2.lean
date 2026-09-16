import Mathlib

def divisors_list_comp (n k : ℕ) : List ℕ :=
  if h : k > n then []
  else if n % k == 0 then k :: divisors_list_comp n (k + 1)
  else divisors_list_comp n (k + 1)
termination_by n + 1 - k

def my_divisors (n : ℕ) : List ℕ := divisors_list_comp n 1

#eval my_divisors 12
