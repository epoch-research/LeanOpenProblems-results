import Mathlib

def P : ℕ := 1093^1093

def dc_mod (fuel a b : ℕ) : ℕ × ℕ :=
  match fuel with
  | 0 => (1, 0)
  | fuel' + 1 =>
    if a + 1 = b then
      let k := a + 1
      let X := k % P
      let Z := if k % 2 == 0 then 1 else P - 1
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

lemma L1 : dc_mod 2 0 4 = (let mid := (0+4)/2; let (X1, Z1) := dc_mod 1 0 mid; let (X2, Z2) := dc_mod 1 mid 4; ((X2 * X1) % P, (X2 * Z1 + Z2 * X1) % P)) := rfl
