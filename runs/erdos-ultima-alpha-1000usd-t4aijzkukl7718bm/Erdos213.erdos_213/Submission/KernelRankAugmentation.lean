import FormalConjecturesUtil

/-! A nonzero pairing with an old kernel vector increases matrix rank.
This is a general linear-algebra lemma, not a geometric rank bound. -/
namespace Erdos213.KernelRankAugmentation
open Matrix
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 200000

lemma rank_submatrix_both_le {m n p q : Type*}
    [Fintype m] [Fintype n] [Fintype p] [Fintype q]
    (A : Matrix m n ℚ) (f : p → m) (g : q → n) :
    (A.submatrix f g).rank≤A.rank := by
  let B := A.submatrix f (Equiv.refl n)
  have h1 : B.rank≤A.rank := Matrix.rank_submatrix_le f (Equiv.refl n) A
  have h2 := Matrix.rank_submatrix_le g (Equiv.refl p) Bᵀ
  rw [← Matrix.rank_transpose (Bᵀ.submatrix g (Equiv.refl p)),
    Matrix.rank_transpose B] at h2
  have h3 : (A.submatrix f g).rank≤B.rank := by
    simpa [B,Matrix.transpose_submatrix,Matrix.submatrix_submatrix,Function.comp_def]
      using h2
  exact h3.trans h1

def augmented {n : Type*} (M : Matrix n n ℚ) (v : n → ℚ) :
    Matrix (n ⊕ Fin 1) (n ⊕ Fin 1) ℚ :=
  fromBlocks M (replicateCol (Fin 1) v) (replicateRow (Fin 1) (-v)) 0

/-- A nonsingular old `m`-minor, together with a kernel vector pairing
nontrivially against the new column, forces rank at least `m+1`. -/
theorem rank_augmented_gt {n : Type*} [Fintype n] [DecidableEq n] {m : ℕ}
    (M : Matrix n n ℚ) (p : Fin m → n) (v k : n → ℚ)
    (hP : (M.submatrix p p).det≠0)
    (hk : ∀ i, (∑ j, M i j*k j)=0)
    (hv : (∑ i, v i*k i)≠0) :
    m<(augmented M v).rank := by
  classical
  let E : Matrix n (Fin m) ℚ := fun i j => if i=p j then 1 else 0
  let U : Matrix (n ⊕ Fin 1) (Fin m ⊕ Fin 1) ℚ :=
    fromBlocks E (replicateCol (Fin 1) k) 0 0
  let rows : Fin m ⊕ Fin 1 → n ⊕ Fin 1 := Sum.map p id
  let P := M.submatrix p p
  let W : Matrix (Fin 1) (Fin m) ℚ := fun _ j => -v (p j)
  let D : Matrix (Fin 1) (Fin 1) ℚ := fun _ _ => -(∑ i, v i*k i)
  have he : ((augmented M v)*U).submatrix rows (Equiv.refl _) =
      fromBlocks P 0 W D := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    all_goals simp [augmented,U,E,rows,P,W,D,Matrix.mul_apply,
      Fintype.sum_sum_type,Matrix.fromBlocks,mul_ite,hk,Finset.sum_neg_distrib]
  have hd : (fromBlocks P (0 : Matrix (Fin m) (Fin 1) ℚ) W D).det≠0 := by
    rw [Matrix.det_fromBlocks_zero₁₂]
    apply mul_ne_zero hP
    simpa [D,Matrix.det_unique] using (neg_ne_zero.mpr hv)
  have hr : (fromBlocks P (0 : Matrix (Fin m) (Fin 1) ℚ) W D).rank=m+1 := by
    have h := Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).mpr
      (isUnit_iff_ne_zero.mpr hd))
    simpa using h
  have hle := Matrix.rank_submatrix_le rows (Equiv.refl (Fin m ⊕ Fin 1))
    ((augmented M v)*U)
  rw [he,hr] at hle
  have hmul := Matrix.rank_mul_le_left (augmented M v) U
  omega

#print axioms rank_submatrix_both_le
#print axioms rank_augmented_gt
end Erdos213.KernelRankAugmentation
