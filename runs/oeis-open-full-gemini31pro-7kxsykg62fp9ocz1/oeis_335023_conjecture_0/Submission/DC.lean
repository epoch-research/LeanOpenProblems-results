import Mathlib

set_option exponentiation.threshold 2000
set_option maxRecDepth 2000000

def P : ℕ := 1093^1093

def dc_mod (a b : ℕ) : ℕ × ℕ :=
  if a + 1 = b then
    let k := a + 1
    let X := k % P
    let Z := if k % 2 == 0 then 1 else P - 1
    (X, Z)
  else if a + 1 < b then
    let mid := (a + b) / 2
    let (X1, Z1) := dc_mod a mid
    let (X2, Z2) := dc_mod mid b
    let X := (X2 * X1) % P
    let Z := (X2 * Z1 + Z2 * X1) % P
    (X, Z)
  else
    (1, 0)
termination_by b - a

lemma dc_mod_eq (a b : ℕ) (h1 : a + 1 ≠ b) (h2 : a + 1 < b) :
  dc_mod a b =
    let mid := (a + b) / 2
    let p1 := dc_mod a mid
    let p2 := dc_mod mid b
    ((p2.1 * p1.1) % P, (p2.1 * p1.2 + p2.2 * p1.1) % P) := by
  conv => lhs; rw [dc_mod.eq_def]
  dsimp
  rw [if_neg h1, if_pos h2]
