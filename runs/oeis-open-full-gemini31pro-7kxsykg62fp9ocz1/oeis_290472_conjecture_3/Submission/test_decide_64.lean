import Submission.Spec
import Mathlib

def a_fast_64 (n : UInt64) : Bool := Id.run do
  let N := 6 * n + 1
  let max_z := (N / 7).toFloat.sqrt.toUInt64
  let mut count := 0
  for z in [0:max_z.toNat + 1] do
    let z64 := z.toUInt64
    let rem1 := N - 7 * z64 * z64
    let max_y := (rem1 / 3).toFloat.sqrt.toUInt64
    for y in [0:max_y.toNat + 1] do
      let y64 := y.toUInt64
      let rem2 := rem1 - 3 * y64 * y64
      -- ensure no underflow by checking if rem1 >= 3*y^2
      if rem1 > 3 * y64 * y64 then
        let x := rem2.toFloat.sqrt.toUInt64
        if x * x == rem2 then
          count := count + 1
          if count > 1 then return true
  return false

def check_all_64 (start_n end_n : ℕ) : Bool :=
  let rec go (n : ℕ) : Bool :=
    if h : n ≥ end_n then
      a_fast_64 n.toUInt64
    else
      if a_fast_64 n.toUInt64 then
        have h_lt : n < end_n := Nat.lt_of_not_ge h
        have : end_n - (n + 1) < end_n - n := by omega
        go (n + 1)
      else false
  go start_n

theorem test : check_all_64 287 100000 = true := by native_decide
