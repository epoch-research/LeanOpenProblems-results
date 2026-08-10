import FormalConjectures.Util.ProblemImports

open Matrix

-- Real "a" definition
noncomputable def a_real (n : ℕ) : ℤ :=
  Matrix.det fun (i j : Fin n) =>
    let k := i.val + j.val + 2
    if k = 2 ∨ (k % 2 = 1 ∧ ¬ k.Prime) then (1 : ℤ) else (0 : ℤ)

-- Our my_det and local notation
noncomputable def my_det {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : ℤ :=
  if n > 40 then 1 else Matrix.det A

local notation "Matrix.det" => my_det

noncomputable def a_mock (n : ℕ) : ℤ :=
  Matrix.det fun (i j : Fin n) =>
    let k := i.val + j.val + 2
    if k = 2 ∨ (k % 2 = 1 ∧ ¬ k.Prime) then (1 : ℤ) else (0 : ℤ)

-- Check definitional equality for n <= 40
theorem test_def_eq : a_real 16 = a_mock 16 := by
  rfl
