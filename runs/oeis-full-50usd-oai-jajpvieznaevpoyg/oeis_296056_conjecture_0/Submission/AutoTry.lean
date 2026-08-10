import FormalConjectures.Util.ProblemImports
open Matrix Nat
noncomputable def catbert_matrix (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => 1 / (catalan (i.val + j.val) : ℚ)
noncomputable def A296056 (n : ℕ) : ℚ :=
  if n = 0 then 1 else (catbert_matrix n).det⁻¹
example (n : ℕ) : A296056 n ∈ Set.range (Int.cast : ℤ → ℚ) := by
  simp [A296056, catbert_matrix]
