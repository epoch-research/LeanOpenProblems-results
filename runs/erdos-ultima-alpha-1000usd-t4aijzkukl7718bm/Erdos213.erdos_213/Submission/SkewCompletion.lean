import Submission.KernelRankAugmentation

/-! Exact alternating-matrix completion rules. These are algebraic conditions,
not Euclidean realization theorems or rational-distance extension theorems. -/
namespace Erdos213.SkewCompletion
open Matrix KernelRankAugmentation
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2000000

lemma skew_dot {n : Type*} [Fintype n] (A : Matrix n n ℚ) (hA : Aᵀ= -A)
    (x y : n → ℚ) : x ⬝ᵥ (A*ᵥy)= -(y ⬝ᵥ (A*ᵥx)) := by
  rw [dotProduct_mulVec,←mulVec_transpose,hA,neg_mulVec,neg_dotProduct,dotProduct_comm]

lemma skew_self {n : Type*} [Fintype n] (A : Matrix n n ℚ) (hA : Aᵀ= -A)
    (x : n → ℚ) : x ⬝ᵥ (A*ᵥx)=0 := by
  have hh := skew_dot A hA x x
  linarith

lemma augmented_skew {n : Type*} (A : Matrix n n ℚ) (hA : Aᵀ= -A)
    (v : n → ℚ) : (augmented A v)ᵀ= -(augmented A v) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · exact congrFun (congrFun hA i) j
  all_goals simp [augmented,Matrix.transpose_apply,Matrix.fromBlocks]

/-- Adjoining a column from the old image is a rectangular congruence.
In particular the new diagonal entry really is zero, by skew-symmetry. -/
lemma augmented_factor {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℚ) (hA : Aᵀ= -A) (q : n → ℚ) :
    augmented A (A*ᵥq) =
      (fromRows 1 (replicateRow (Fin 1) q))*A*
      (fromRows 1 (replicateRow (Fin 1) q))ᵀ := by
  let R : Matrix (Fin 1) n ℚ := replicateRow (Fin 1) q
  have hr : q ᵥ* A= -(A*ᵥq) := by rw [←mulVec_transpose,hA,neg_mulVec]
  have hRA : R*A=replicateRow (Fin 1) (-(A*ᵥq)) := by
    ext i j
    change (q ᵥ* A) j=(-(A*ᵥq)) j
    rw [hr]
  have hAR : A*Rᵀ=replicateCol (Fin 1) (A*ᵥq) := by
    ext i j
    rfl
  have hRAR : (R*A)*Rᵀ=0 := by
    rw [hRA]
    ext i j
    change (-(A*ᵥq)) ⬝ᵥ q=0
    rw [neg_dotProduct,dotProduct_comm,skew_self A hA q,neg_zero]
  change augmented A (A*ᵥq)=(fromRows 1 R)*A*(fromRows 1 R)ᵀ
  rw [transpose_fromRows,transpose_one,fromRows_mul,one_mul,fromRows_mul_fromCols,
    Matrix.mul_one,Matrix.mul_one,hRAR,hAR,hRA]
  rfl

/-- The exact rank is unchanged; no nonsingularity hypothesis is needed
when the new column is already in the old image. -/
theorem rank_augmented_image {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℚ) (hA : Aᵀ= -A) (q : n → ℚ) :
    (augmented A (A*ᵥq)).rank=A.rank := by
  apply le_antisymm
  · rw [augmented_factor A hA q]
    exact (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)
  · have hh := rank_submatrix_both_le (augmented A (A*ᵥq)) Sum.inl Sum.inl
    simpa [augmented] using hh

/-- For a nonsingular alternating base matrix, ANY first column preserves
rank. Thus this rank condition alone supplies no new metric equation. -/
theorem rank_augmented_nonsingular {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℚ) (hA : Aᵀ= -A) (hdet : A.det≠0) (v : n → ℚ) :
    (augmented A v).rank=Fintype.card n := by
  have hv : A*ᵥ(A⁻¹*ᵥv)=v := by
    rw [mulVec_mulVec,mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hdet),one_mulVec]
  rw [←hv,rank_augmented_image A hA]
  exact rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet))

def kernelVector {n : Type*} (q : n → ℚ) : n ⊕ Fin 1 → ℚ :=
  Sum.elim (-q) (fun _ => 1)

def nextColumn {n : Type*} (u : n → ℚ) (d : ℚ) : n ⊕ Fin 1 → ℚ :=
  Sum.elim u (fun _ => d)

lemma kernelVector_annihilates {n : Type*} [Fintype n]
    (A : Matrix n n ℚ) (hA : Aᵀ= -A) (q : n → ℚ) :
    (augmented A (A*ᵥq))*ᵥkernelVector q=0 := by
  have hh : (A*ᵥq) ⬝ᵥ q=0 := by rw [dotProduct_comm]; exact skew_self A hA q
  ext i
  rcases i with i | i
  · simp [augmented,kernelVector,Matrix.mulVec,dotProduct,Fintype.sum_sum_type,
      Finset.sum_neg_distrib]
  · simpa [augmented,kernelVector,Matrix.mulVec,dotProduct,Fintype.sum_sum_type] using hh

lemma kernel_pairing {n : Type*} [Fintype n] (q u : n → ℚ) (d : ℚ) :
    (nextColumn u d) ⬝ᵥ kernelVector q=d-q ⬝ᵥ u := by
  simp [nextColumn,kernelVector,dotProduct,Fintype.sum_sum_type,Finset.sum_neg_distrib,
    mul_comm]
  ring

/-- Once one column has been adjoined, a second rank-preserving column
has a genuine bilinear compatibility condition on the new signed edge. -/
theorem second_column_necessary (n : ℕ) (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : Aᵀ= -A) (hdet : A.det≠0) (q u : Fin n → ℚ) (d : ℚ)
    (hrank : (augmented (augmented A (A*ᵥq)) (nextColumn u d)).rank≤n) :
    d=q ⬝ᵥ u := by
  by_contra hd
  have hP : ((augmented A (A*ᵥq)).submatrix Sum.inl Sum.inl).det≠0 := by
    simpa [augmented] using hdet
  have hk : ∀ i, (∑ j, augmented A (A*ᵥq) i j*kernelVector q j)=0 := by
    intro i
    exact congrFun (kernelVector_annihilates A hA q) i
  have hv : (∑ i, nextColumn u d i*kernelVector q i)≠0 := by
    change (nextColumn u d) ⬝ᵥ kernelVector q≠0
    rw [kernel_pairing]
    exact sub_ne_zero.mpr hd
  have hh := rank_augmented_gt (augmented A (A*ᵥq)) Sum.inl (nextColumn u d)
    (kernelVector q) hP hk hv
  omega

/-- The bilinear compatibility condition is sufficient for the matrix rank
condition too. It is still not sufficient for Euclidean realization. -/
theorem second_column_sufficient {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℚ) (hA : Aᵀ= -A) (q r : n → ℚ) :
    (augmented (augmented A (A*ᵥq)) (nextColumn (A*ᵥr) (q ⬝ᵥ (A*ᵥr)))).rank=A.rank := by
  let w : n ⊕ Fin 1 → ℚ := Sum.elim r (fun _ => 0)
  have hw : (augmented A (A*ᵥq))*ᵥw=nextColumn (A*ᵥr) (q ⬝ᵥ (A*ᵥr)) := by
    ext i
    rcases i with i | i
    · simp [augmented,w,nextColumn,Matrix.mulVec,dotProduct,Fintype.sum_sum_type]
    · have hh := skew_dot A hA q r
      rw [dotProduct_comm r (A*ᵥq)] at hh
      simp only [dotProduct] at hh
      simpa [augmented,w,nextColumn,Matrix.mulVec,dotProduct,Fintype.sum_sum_type,
        Finset.sum_neg_distrib] using hh.symm
  rw [←hw,rank_augmented_image _ (augmented_skew A hA _) w,
    rank_augmented_image A hA q]

/-- The exact two-column criterion in terms of the original columns,
without supplying preimages as extra data. No metric realization is inferred. -/
theorem two_column_rank_iff (n : ℕ) (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : Aᵀ= -A) (hdet : A.det≠0) (v u : Fin n → ℚ) (d : ℚ) :
    (augmented (augmented A v) (nextColumn u d)).rank=n ↔
      d=(A⁻¹*ᵥv) ⬝ᵥ u := by
  have hV : A*ᵥ(A⁻¹*ᵥv)=v := by
    rw [mulVec_mulVec,mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hdet),one_mulVec]
  have hU : A*ᵥ(A⁻¹*ᵥu)=u := by
    rw [mulVec_mulVec,mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hdet),one_mulVec]
  have hArank : A.rank=n := by
    have hh := rank_of_isUnit A ((Matrix.isUnit_iff_isUnit_det _).mpr
      (isUnit_iff_ne_zero.mpr hdet))
    simpa using hh
  constructor
  · intro hr
    apply second_column_necessary n A hA hdet (A⁻¹*ᵥv) u d
    rw [hV,hr]
  · intro hd
    have hh := second_column_sufficient A hA (A⁻¹*ᵥv) (A⁻¹*ᵥu)
    rwa [hV,hU,←hd,hArank] at hh

#print axioms two_column_rank_iff
#print axioms augmented_factor
#print axioms rank_augmented_image
#print axioms rank_augmented_nonsingular
#print axioms kernelVector_annihilates
#print axioms second_column_necessary
#print axioms second_column_sufficient
end
end Erdos213.SkewCompletion
