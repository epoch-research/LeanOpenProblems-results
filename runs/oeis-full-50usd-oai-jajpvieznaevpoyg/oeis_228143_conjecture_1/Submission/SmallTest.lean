import FormalConjectures.Util.ProblemImports
open BigOperators Matrix Nat

def A005259' (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun k =>
    (n.choose k)^2 * ((Nat.choose (n + k) k))^2
noncomputable def a (n : ℕ) : ℕ :=
  let dim : Type := Fin (n + 1)
  let M : Matrix dim dim ℤ :=
    Matrix.of fun i j => (A005259' (i.val + j.val) : ℤ)
  M.det.natAbs

example : (16 * 3^1) ∣ a 1 := by
  unfold a; simp only; rw [Matrix.det_fin_two]; native_decide
example : (16 * 3^2) ∣ a 2 := by
  unfold a; simp only; rw [Matrix.det_fin_three]; native_decide
example : (16 * 3^3) ∣ a 3 := by
  unfold a; simp only; rw [Matrix.det_apply]; native_decide
