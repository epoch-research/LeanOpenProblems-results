import Mathlib

def my_set (n k : ℕ) : Finset ℕ :=
  { n + k + 1, n + k - 1, n - k + 1, n - k - 1 }

#eval (my_set 3 1).card
