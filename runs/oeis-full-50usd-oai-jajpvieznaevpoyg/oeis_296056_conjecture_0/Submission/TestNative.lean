import FormalConjectures.Util.ProblemImports
open Matrix Nat
noncomputable def catbert_matrix2 (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => 1 / (catalan (i.val + j.val) : ℚ)
noncomputable def A2960562 (n : ℕ) : ℚ :=
  if n = 0 then 1 else (catbert_matrix2 n).det⁻¹
example (n : ℕ) : (A2960562 n).den = 1 := by
  native_decide +revert
