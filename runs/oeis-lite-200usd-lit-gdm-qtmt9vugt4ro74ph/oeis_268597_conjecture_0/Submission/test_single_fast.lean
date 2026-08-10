import Mathlib
set_option maxRecDepth 200000

open Nat

def fast_totient_aux (n : ℕ) : ℕ → ℕ → ℕ
  | 0, acc => acc
  | k + 1, acc => fast_totient_aux n k (acc + (if n.Coprime (k + 1) then 1 else 0))

def fast_totient (n : ℕ) : ℕ := fast_totient_aux n n 0

example : fast_totient 1352 = 576 := by decide
example : fast_totient 8587 = 8586 := by decide
