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

example : (4 : ZMod 3) = 1 := by
  rw [ZMod.natCast_eq_natCast_iff]
  norm_num
example : (2 : ZMod 3) = -1 := by
  rw [← sub_eq_zero]
  rw [← ZMod.natCast_eq_zero_iff]
  norm_num

lemma A0 : A005259' 0 = 1 := by norm_num [A005259']
lemma A1 : A005259' 1 = 5 := by norm_num [A005259']
lemma A2 : A005259' 2 = 73 := by norm_num [A005259']
lemma A3 : A005259' 3 = 1445 := by norm_num [A005259']
lemma A4 : A005259' 4 = 33001 := by norm_num [A005259']
lemma A5 : A005259' 5 = 819005 := by norm_num [A005259']
lemma A6 : A005259' 6 = 21460825 := by norm_num [A005259']

example : (16 * 3^1) ∣ a 1 := by
  unfold a
  simp only
  rw [Matrix.det_fin_two]
  rw [A0,A1,A2]
  norm_num
example : (16 * 3^2) ∣ a 2 := by
  unfold a
  simp only
  rw [Matrix.det_fin_three]
  rw [A0,A1,A2,A3,A4]
  norm_num
example : (16 * 3^3) ∣ a 3 := by
  unfold a
  simp only
  rw [Matrix.det_apply]
  rw [A0,A1,A2,A3,A4,A5,A6]
  norm_num
example : a 0 = 1 := by
  unfold a
  simp only
  rw [Matrix.det_fin_one]
  rw [A0]
  norm_num
