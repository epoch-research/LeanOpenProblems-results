import Submission.MatrixCertificates

/-! A balancing obstruction for matrix carry certificates. This is not a
solution of Erdős 406 and asserts no sufficient certificate. -/
namespace Erdos406MatrixRigidity
open scoped BigOperators Matrix

variable {σ : Type*} [Fintype σ]

noncomputable def weight (l r : σ → ℝ) (M : Matrix σ σ ℝ) : ℝ :=
  ∑ i, ∑ j, l i * M i j * r j

lemma weight_add (l r : σ → ℝ) (M N : Matrix σ σ ℝ) :
    weight l r (M + N) = weight l r M + weight l r N := by
  simp only [weight, Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

lemma weight_sub (l r : σ → ℝ) (M N : Matrix σ σ ℝ) :
    weight l r (M - N) = weight l r M - weight l r N := by
  simp only [weight, Matrix.sub_apply, mul_sub, sub_mul, Finset.sum_sub_distrib]

lemma weight_eq_dot (l r : σ → ℝ) (M : Matrix σ σ ℝ) :
    weight l r M = l ⬝ᵥ (M *ᵥ r) := by
  simp only [weight, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

lemma weight_nonneg (l r : σ → ℝ) (hl : ∀ i, 0 ≤ l i) (hr : ∀ i, 0 ≤ r i)
    (M : Matrix σ σ ℝ) (hM : ∀ i j, 0 ≤ M i j) : 0 ≤ weight l r M := by
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (mul_nonneg (hl i) (hM i j)) (hr j)

lemma weight_sum {ι : Type*} [Fintype ι] (l r : σ → ℝ)
    (M : ι → Matrix σ σ ℝ) :
    weight l r (∑ k, M k) = ∑ k, weight l r (M k) := by
  simp only [weight, Matrix.sum_apply, Finset.sum_mul, Finset.mul_sum]
  calc
    (∑ i, ∑ j, ∑ k, l i * M k i j * r j) =
        ∑ i, ∑ k, ∑ j, l i * M k i j * r j := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

lemma weight_commutator (l r : σ → ℝ) (T U : Matrix σ σ ℝ) (t : ℝ)
    (hl : Matrix.vecMul l T = t • l) (hr : T *ᵥ r = t • r) :
    weight l r (T * U - U * T) = 0 := by
  rw [weight_sub, weight_eq_dot, weight_eq_dot,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, hl, hr]
  simp [Matrix.mulVec_smul, dotProduct, mul_left_comm, mul_assoc]

lemma nonneg_eq_zero_of_weight_eq_zero (l r : σ → ℝ)
    (hl : ∀ i, 0 < l i) (hr : ∀ i, 0 < r i)
    (M : Matrix σ σ ℝ) (hM : ∀ i j, 0 ≤ M i j)
    (hw : weight l r M = 0) : M = 0 := by
  have hterm : ∀ i j, 0 ≤ l i * M i j * r j := fun i j =>
    mul_nonneg (mul_nonneg (hl i).le (hM i j)) (hr j).le
  have hrow : ∀ i, 0 ≤ ∑ j, l i * M i j * r j := fun i =>
    Finset.sum_nonneg (fun j _ => hterm i j)
  have hrows := (Fintype.sum_eq_zero_iff_of_nonneg hrow).mp hw
  ext i j
  have hrowi : (∑ j, l i * M i j * r j) = 0 := congrFun hrows i
  have hij := congrFun ((Fintype.sum_eq_zero_iff_of_nonneg (hterm i)).mp hrowi) j
  simpa only [Matrix.zero_apply] using
    (mul_eq_zero.mp hij).resolve_right (ne_of_gt (hr j)) |>
      fun hh => (mul_eq_zero.mp hh).resolve_left (ne_of_gt (hl i))

set_option maxHeartbeats 2000000 in
lemma carry_balance (A H : ℕ → Matrix σ σ ℝ) :
    (∑ k : Fin 12, (A (k.val % 3) * H (k.val / 3) -
      H (k.val % 4) * A (k.val / 4))) =
    (A 0 + A 1 + A 2) * (H 0 + H 1 + H 2 + H 3) -
    (H 0 + H 1 + H 2 + H 3) * (A 0 + A 1 + A 2) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ]
  norm_num only [Nat.zero_mod, Nat.zero_div, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv,
    Finset.sum_empty, add_zero]
  noncomm_ring

/-- If the total digit matrix has positive left and right eigenvectors at
one eigenvalue, all twelve entrywise carry inequalities are equalities. -/
theorem positive_balance_rigidity (A H : ℕ → Matrix σ σ ℝ)
    (l r : σ → ℝ) (t : ℝ) (hl : ∀ i, 0 < l i) (hr : ∀ i, 0 < r i)
    (heigl : Matrix.vecMul l (A 0 + A 1 + A 2) = t • l)
    (heigr : (A 0 + A 1 + A 2) *ᵥ r = t • r)
    (hstep : ∀ c d e cp, c < 4 → d < 3 → e < 3 → cp < 4 →
      4 * d + cp = 3 * c + e → ∀ i j, (H cp * A d) i j ≤ (A e * H c) i j) :
    ∀ c d e cp, c < 4 → d < 3 → e < 3 → cp < 4 →
      4 * d + cp = 3 * c + e → H cp * A d = A e * H c := by
  let S : Fin 12 → Matrix σ σ ℝ := fun k =>
    A (k.val % 3) * H (k.val / 3) - H (k.val % 4) * A (k.val / 4)
  have hS : ∀ k i j, 0 ≤ S k i j := by
    intro k i j
    dsimp [S]
    apply sub_nonneg.mpr
    apply hstep (k.val / 3) (k.val / 4) (k.val % 3) (k.val % 4)
      (by omega) (by omega) (by omega) (by omega) (by omega)
  have hW : ∀ k, 0 ≤ weight l r (S k) := fun k =>
    weight_nonneg l r (fun i => (hl i).le) (fun i => (hr i).le) (S k) (hS k)
  have hsum : ∑ k, weight l r (S k) = 0 := by
    rw [← weight_sum]
    rw [carry_balance]
    exact weight_commutator l r _ _ t heigl heigr
  have hzero : ∀ k, S k = 0 := fun k =>
    nonneg_eq_zero_of_weight_eq_zero l r hl hr (S k) (hS k)
      (congrFun ((Fintype.sum_eq_zero_iff_of_nonneg hW).mp hsum) k)
  intro c d e cp hc hd he hcp heq
  let k : Fin 12 := ⟨4 * d + cp, by omega⟩
  have hk := hzero k
  have hk3 : k.val % 3 = e := by dsimp [k]; omega
  have hk3' : k.val / 3 = c := by dsimp [k]; omega
  have hk4 : k.val % 4 = cp := by dsimp [k]; omega
  have hk4' : k.val / 4 = d := by dsimp [k]; omega
  dsimp [S] at hk
  rw [hk3, hk3', hk4, hk4'] at hk
  exact (sub_eq_zero.mp hk).symm

#print axioms positive_balance_rigidity
end Erdos406MatrixRigidity
