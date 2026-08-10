import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 500000
set_option maxHeartbeats 2000000
open Nat
open scoped ArithmeticFunction.sigma

def a (n : ℕ) : ℤ :=
  (divisors n).sum fun d =>
    (2 * d : ℤ) - (ArithmeticFunction.sigma 1 d : ℤ)

def check_range (start len : ℕ) : Bool :=
  match len with
  | 0 => true
  | len' + 1 =>
    let n := start + len'
    (decide (n.Prime) || decide (a n ≠ 1)) && check_range start len'

theorem test_dec_1 : check_range 501 1500 = true := by
  decide
