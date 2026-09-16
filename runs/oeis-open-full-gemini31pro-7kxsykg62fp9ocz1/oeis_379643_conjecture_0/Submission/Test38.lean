import Mathlib

def b_func (n : ℕ) : ℤ :=
  let b (b : ℕ) : ℕ := b + 1
  b 5

#eval b_func 0
