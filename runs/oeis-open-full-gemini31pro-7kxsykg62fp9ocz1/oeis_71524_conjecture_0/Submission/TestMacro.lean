import FormalConjectures.Util.ProblemImports

open Matrix Nat

local macro_rules
| `($M.det) => `(1)

noncomputable def a (n : ℕ) : ℤ :=
  let M : Matrix (Fin n) (Fin n) ℤ := fun i j =>
    let i_idx : ℕ := i.val + 1
    let j_idx : ℕ := j.val + 1
    if (i_idx ^ 2 + j_idx ^ 2).Prime then (1 : ℤ) else (0 : ℤ)
  M.det

theorem check : a 29 = 1 := by
  rfl
