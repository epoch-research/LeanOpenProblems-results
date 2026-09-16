import Mathlib

set_option maxHeartbeats 100000000

def M : ℕ := 1194648
def P : ℕ := 1093^1092

def dc_mod (fuel a b : ℕ) : ℕ × ℕ × ℕ :=
  match fuel with
  | 0 => (1, 1, 0)
  | fuel' + 1 =>
    if a + 1 = b then
      let k := a + 1
      let X := k % P
      let Y := k % P
      let Z := if k % 2 == 0 then k % P else (P - k % P) % P
      (X, Y, Z)
    else if a + 1 < b then
      let mid := (a + b) / 2
      let (X1, Y1, Z1) := dc_mod fuel' a mid
      let (X2, Y2, Z2) := dc_mod fuel' mid b
      let X := (X2 * X1) % P
      let Y := (Y2 * Y1) % P
      let Z := (Y2 * Z1 + Z2 * X1) % P
      (X, Y, Z)
    else
      (1, 1, 0)

theorem F_mod_P_dc : (dc_mod 25 0 M).2.2 = 0 := by decide
