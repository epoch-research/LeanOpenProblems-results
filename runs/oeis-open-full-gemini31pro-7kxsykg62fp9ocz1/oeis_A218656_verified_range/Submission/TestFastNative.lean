import Mathlib

def check_one (n : ℕ) (k rem : ℕ) : Bool :=
  match rem with
  | 0 => false
  | rem' + 1 =>
      let val := k ^ 4 + (2 * n + 1 - k) ^ 4
      if val.minFac == val then true
      else check_one n (k + 1) rem'

def check_all (m : ℕ) (n rem : ℕ) : Bool :=
  match rem with
  | 0 => true
  | rem' + 1 =>
      if check_one n 1 n then check_all m (n + 1) rem'
      else false

theorem test_all : check_all 1000 1 1000 = true := by native_decide
