import Submission.Spec

def catbert_matrix_comp (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => 1 / (catalan (i.val + j.val) : ℚ)

lemma catbert_matrix_eq (n : ℕ) : catbert_matrix n = catbert_matrix_comp n := rfl
