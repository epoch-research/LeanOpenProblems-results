import Mathlib

def b_A145062 (k : ℕ) : ℕ :=
  match k with
  | 0 => 1
  | k_plus_1 => if k_plus_1 % 2 = 0 then k_plus_1 / 2 + 1 else 0

noncomputable def A145062_aux : ℕ → ℕ → ℕ
| 0, 0 => 1
| 0, _ => 0
| n + 1, k =>
  let prev_A := A145062_aux n
  let down_step_contrib := prev_A (k + 1)
  let up_step_contrib := if k = 0 then 0 else prev_A (k - 1)
  let level_step_contrib := b_A145062 k * prev_A k
  down_step_contrib + up_step_contrib + level_step_contrib

noncomputable def a (n : ℕ) : ℕ := A145062_aux n 0

#eval a 0
#eval a 1
#eval a 2
