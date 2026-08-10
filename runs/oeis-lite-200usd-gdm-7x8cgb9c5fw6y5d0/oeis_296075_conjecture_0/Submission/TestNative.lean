import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 500000
set_option maxHeartbeats 2000000
open Nat

def sum_divs_aux (n i : ℕ) (acc : ℕ) : ℕ :=
  match i with
  | 0 => acc
  | i' + 1 =>
    if (i' + 1) ∣ n then
      sum_divs_aux n i' (acc + i' + 1)
    else
      sum_divs_aux n i' acc

def sigma_fast (n : ℕ) : ℕ :=
  sum_divs_aux n n 0

def a_fast_aux (n i : ℕ) (acc : ℤ) : ℤ :=
  match i with
  | 0 => acc
  | i' + 1 =>
    let d := i' + 1
    if d ∣ n then
      a_fast_aux n i' (acc + 2 * (d : ℤ) - (sigma_fast d : ℤ))
    else
      a_fast_aux n i' acc

def a_fast (n : ℕ) : ℤ :=
  a_fast_aux n n 0

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

