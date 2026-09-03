import Submission.BinaryCriticalRecurrenceObstruction

/-! Nonnegative finite antidifferences cannot coexist with positive affine
lower growth. These lemmas reject fixed potential models, not Erdős 406. -/
namespace Erdos406BinaryCriticalRecurrence
open scoped Matrix BigOperators

lemma nonnegative_filter_lower (d : ℕ) (w : Fin d → ℝ)
    (hw : ∀ i, 0 ≤ w i) (f : ℕ → ℝ) (a b : ℝ) (ha : 0 ≤ a)
    (hlower : ∀ n : ℕ, a*n-b ≤ f n) (n : ℕ) :
    (a*(∑ i, w i))*n-b*(∑ i, w i) ≤ ∑ i, w i*f (n+i.val) := by
  have hh : ∑ i, w i*(a*n-b) ≤ ∑ i, w i*f (n+i.val) := by
    apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_left _ (hw i)
    have h := hlower (n+i.val)
    have hn : (0 : ℝ) ≤ a*i.val := mul_nonneg ha (Nat.cast_nonneg _)
    push_cast at h
    nlinarith
  rw [← Finset.sum_mul] at hh
  nlinarith

/-- If `(1-X)*A(X)` acts as the identity on a sequence and `A` has
nonnegative coefficients with positive sum, the sequence cannot have a
positive affine lower bound. There is no restriction on the error offset. -/
theorem antidifference_no_positive_linear_lower (d : ℕ) (w : Fin d → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hwpos : 0 < ∑ i, w i) (f : ℕ → ℝ)
    (hrec : ∀ n : ℕ, (∑ i, w i*f (n+i.val)) -
      (∑ i, w i*f (n+i.val+1)) = f n) :
    ¬ ∃ a b : ℝ, 0 < a ∧ ∀ n : ℕ, a*n-b ≤ f n := by
  rintro ⟨a,b,ha,hlower⟩
  obtain ⟨K,hK⟩ := exists_nat_gt (b/a)
  have hK' : b < a*K := by
    have := (div_lt_iff₀ ha).mp hK
    nlinarith
  let F : ℕ → ℝ := fun n => f (K+n)
  have hF : ∀ n : ℕ, a*n-(b-a*K) ≤ F n := by
    intro n
    have h := hlower (K+n)
    push_cast at h
    dsimp [F]
    linarith
  let g : ℕ → ℝ := fun n => ∑ i, w i*F (n+i.val)
  have hg : ∀ n : ℕ, (a*(∑ i, w i))*n-(b-a*K)*(∑ i, w i) ≤ g n :=
    nonnegative_filter_lower d w hw F a (b-a*K) ha.le hF
  obtain ⟨m,hm⟩ := linear_lower_min_attained g (a*(∑ i, w i))
    ((b-a*K)*(∑ i, w i)) (mul_pos ha hwpos) hg
  have hpos : 0 < F m := by
    have hh := hF m
    have hn : (0 : ℝ) ≤ a*m := mul_nonneg ha.le (Nat.cast_nonneg _)
    linarith
  have hr : g m-g (m+1) = F m := by
    simpa only [g,F,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hrec (K+m)
  have hmin := hm (m+1)
  linarith

/-- Evaluation of a polynomial filter on a scalar matrix orbit. -/
lemma matrix_filter_value (N d : ℕ) (M : Matrix (Fin N) (Fin N) ℝ)
    (u v : Fin N → ℝ) (w : Fin d → ℝ) (n : ℕ) :
    (∑ i, w i*(u ⬝ᵥ ((M^(n+i.val))*ᵥ v))) =
      u ⬝ᵥ ((M^n*(∑ i, w i • M^i.val))*ᵥ v) := by
  simp only [Finset.mul_sum, Matrix.mul_smul, Matrix.sum_mulVec,
    Matrix.smul_mulVec, dotProduct_sum, dotProduct_smul, smul_eq_mul, pow_add]

/-- The matrix identity is a sufficient, finite exact certificate. It does
not assert that every matrix with a given spectral property admits one. -/
theorem matrix_antidifference_obstruction (N d : ℕ)
    (M : Matrix (Fin N) (Fin N) ℝ) (w : Fin d → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hwpos : 0 < ∑ i, w i)
    (hid : (1-M)*(∑ i, w i • M^i.val) = 1) (u v : Fin N → ℝ) :
    ¬ ∃ a b : ℝ, 0 < a ∧ ∀ n : ℕ, a*n-b ≤ u ⬝ᵥ ((M^n)*ᵥ v) := by
  apply antidifference_no_positive_linear_lower d w hw hwpos
    (fun n => u ⬝ᵥ ((M^n)*ᵥ v))
  intro n
  have hshift : (∑ i, w i*(u ⬝ᵥ ((M^(n+i.val+1))*ᵥ v))) =
      u ⬝ᵥ ((M^(n+1)*(∑ i, w i • M^i.val))*ᵥ v) := by
    simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using
      matrix_filter_value N d M u v w (n+1)
  rw [matrix_filter_value, hshift, ← dotProduct_sub, ← Matrix.sub_mulVec]
  have hm : M^n*(∑ i, w i • M^i.val)-
      M^(n+1)*(∑ i, w i • M^i.val) = M^n := by
    rw [pow_succ, ← sub_mul, ← mul_one_sub, mul_assoc, hid, mul_one]
  rw [hm]

#print axioms matrix_filter_value
#print axioms matrix_antidifference_obstruction
#print axioms nonnegative_filter_lower
#print axioms antidifference_no_positive_linear_lower
end Erdos406BinaryCriticalRecurrence
