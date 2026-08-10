import FormalConjectures.Util.ProblemImports

set_option exponentiation.threshold 30000
set_option maxRecDepth 10000

open Nat ZMod

def f_seq (M : ℕ) : ℕ → (ZMod M → ZMod M)
  | 0 => fun z => z ^ 10
  | i + 1 => fun z => f_seq M i (f_seq M i z)

theorem test_13 : f_seq (10^(2^13) + 1) 13 3 ≠ 1 := by
  decide
