import Submission.Spec

open Nat MvPolynomial BigOperators

noncomputable def U : MvPolynomial (Fin 3) ℤ := 1 + MvPolynomial.X 0
noncomputable def V : MvPolynomial (Fin 3) ℤ := MvPolynomial.X 1 + MvPolynomial.X 2
noncomputable def W : MvPolynomial (Fin 3) ℤ := MvPolynomial.X 1 - MvPolynomial.X 2

theorem P_n_decomp (n : ℕ) :
  P_n n = (U + V) ^ (2 * n) * (U ^ 2 - W ^ 2) ^ n := by
  dsimp [P_n, U, V, W]
  ring

