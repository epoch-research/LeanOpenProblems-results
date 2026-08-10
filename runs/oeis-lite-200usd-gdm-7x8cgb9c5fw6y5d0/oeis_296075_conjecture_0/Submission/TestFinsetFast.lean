import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 500000
set_option maxHeartbeats 2000000
open Nat
open scoped ArithmeticFunction.sigma

def a (n : ℕ) : ℤ :=
  (divisors n).sum fun d =>
    (2 * d : ℤ) - (ArithmeticFunction.sigma 1 d : ℤ)

def sigma_fast (n : ℕ) : ℤ :=
  (divisors n).sum (fun d => (d : ℤ))

def a_fast (n : ℕ) : ℤ :=
  (divisors n).sum fun d => (2 * d : ℤ) - sigma_fast d

def check_range_fast (start len : ℕ) : Bool :=
  match len with
  | 0 => true
  | len' + 1 =>
    let n := start + len'
    decide (a_fast n ≠ 1) && check_range_fast start len'

theorem test_0 : check_range_fast 13 100 = true := by decide
theorem test_1 : check_range_fast 113 100 = true := by decide
theorem test_2 : check_range_fast 213 100 = true := by decide
theorem test_3 : check_range_fast 313 100 = true := by decide
theorem test_4 : check_range_fast 413 100 = true := by decide
theorem test_5 : check_range_fast 513 100 = true := by decide
theorem test_6 : check_range_fast 613 100 = true := by decide
theorem test_7 : check_range_fast 713 100 = true := by decide
theorem test_8 : check_range_fast 813 100 = true := by decide
theorem test_9 : check_range_fast 913 88 = true := by decide
