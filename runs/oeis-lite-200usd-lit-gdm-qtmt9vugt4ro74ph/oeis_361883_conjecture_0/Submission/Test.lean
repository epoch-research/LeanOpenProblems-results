import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

open Nat Finset

def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    (∑ k ∈ range (n + 1), (n + 2 * k) * choose (n + k - 1) k ^ 3) / n

example : a 1 = 4 := by rfl
example : a 2 = 98 := by rfl
example : a 3 = 3550 := by rfl
example : a 4 = 150722 := by rfl
example : a 5 = 6993504 := by rfl

example : a 6 = 343542572 := by rfl
example : a 7 = 17560824138 := by rfl
example : a 8 = 924397069250 := by rfl
example : a 9 = 49770307114528 := by rfl
example : a 10 = 2728028537409848 := by rfl