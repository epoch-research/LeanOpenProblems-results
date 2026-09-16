import Mathlib

set_option exponentiation.threshold 2000
set_option maxHeartbeats 20000000

def M : ℕ := 1194648
def P : ℕ := 1093^1092

def dc_mod (fuel a b : ℕ) : ℕ × ℕ :=
  match fuel with
  | 0 => (1, 0)
  | fuel' + 1 =>
    if a + 1 = b then
      let k := a + 1
      let X := k % P
      let Z := if k % 2 == 0 then k % P else (P - k % P) % P
      (X, Z)
    else if a + 1 < b then
      let mid := (a + b) / 2
      let (X1, Z1) := dc_mod fuel' a mid
      let (X2, Z2) := dc_mod fuel' mid b
      let X := (X2 * X1) % P
      let Z := (X2 * Z1 + Z2 * X1) % P
      (X, Z)
    else
      (1, 0)

-- We test decide
theorem test_100000 : (dc_mod 21 0 100000).2 = 4786435017120 := by decide
