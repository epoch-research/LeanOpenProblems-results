import Mathlib

def P : ℤ := 1093^1093

def dc_mod (fuel a b : ℕ) : ℤ × ℤ :=
  match fuel with
  | 0 => (1, 0)
  | fuel' + 1 =>
    if a + 1 = b then
      let k : ℤ := a + 1
      let X := k % P
      let Z := if (a + 1) % 2 == 0 then 1 else -1
      (X, Z % P)
    else if a + 1 < b then
      let mid := (a + b) / 2
      let (X1, Z1) := dc_mod fuel' a mid
      let (X2, Z2) := dc_mod fuel' mid b
      let X := (X2 * X1) % P
      let Z := (X2 * Z1 + Z2 * X1) % P
      (X, Z)
    else
      (1, 0)

set_option exponentiation.threshold 2000
theorem test_int : (dc_mod 21 0 100).2 = -1632612711680 := by decide
