import Mathlib

def P : ℕ := 1093
def P2 : ℕ := 1194649

def dc_fast (fuel a b : ℕ) : ℕ × ℕ :=
  match fuel with
  | 0 => (1, 0)
  | fuel' + 1 =>
    if a + 1 = b then
      let k := a + 1
      let sign := if k % 2 == 0 then 1 else P2 - 1
      if k % P == 0 then
        let D := k / P
        let N := sign
        (D % P2, N % P2)
      else
        let D := k
        let N := (sign * P) % P2
        (D % P2, N % P2)
    else if a + 1 < b then
      let mid := (a + b) / 2
      let (X1, Z1) := dc_fast fuel' a mid
      let (X2, Z2) := dc_fast fuel' mid b
      let X := (X1 * X2) % P2
      let Z := (X2 * Z1 + X1 * Z2) % P2
      (X, Z)
    else
      (1, 0)

set_option maxHeartbeats 2000000000
theorem main_eval : dc_fast 21 0 1194648 = (264507, 130067) := by decide
