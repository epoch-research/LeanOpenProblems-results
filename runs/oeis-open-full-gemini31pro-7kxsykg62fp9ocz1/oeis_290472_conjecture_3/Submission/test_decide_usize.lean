import Mathlib

def a_fast_usize (n : USize) : Bool := Id.run do
  let N := 6 * n + 1
  let max_z := (N / 7).toNat.toFloat.sqrt.toUSize
  let mut count := 0
  for z in [0:max_z.toNat + 1] do
    let zU := z.toUSize
    let rem1 := N - 7 * zU * zU
    let max_y := (rem1 / 3).toNat.toFloat.sqrt.toUSize
    for y in [0:max_y.toNat + 1] do
      let yU := y.toUSize
      let rem2 := rem1 - 3 * yU * yU
      if rem1 > 3 * yU * yU then
        let x := rem2.toNat.toFloat.sqrt.toUSize
        if x * x == rem2 then
          count := count + 1
          if count > 1 then return true
  return false

def check_all_usize (start_n end_n : ℕ) : Bool :=
  let rec go (n : ℕ) : Bool :=
    if h : n ≥ end_n then
      a_fast_usize (USize.ofNat n)
    else
      if a_fast_usize (USize.ofNat n) then
        have h_lt : n < end_n := Nat.lt_of_not_ge h
        have : end_n - (n + 1) < end_n - n := by omega
        go (n + 1)
      else false
  go start_n

theorem test : check_all_usize 287 100000 = true := by native_decide
