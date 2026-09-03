import Submission.AxisBaseCompleteness
import Submission.NormalizedPfaffian
import Submission.KernelRankAugmentation

/-! A complete normalized augmented-rank obstruction for one non-GP metric.
This does not disprove Erdős 213: the control contains collinear triples. -/
namespace Erdos213.AxisGlobalRankObstruction
open Matrix AxisRankObstruction AxisBaseCompleteness KernelRankAugmentation
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 200000

def qModel (b : Fin 42) : Matrix (Fin 8) (Fin 8) ℚ := fun i j => models b i j
def qColumn (t : Fin 7 → Bool) : Fin 8 → ℚ := fun i => extensionColumn t i
def qKernel0 (b : Fin 42) : Fin 8 → ℚ := fun i => kernel0 b i
def qKernel1 (b : Fin 42) : Fin 8 → ℚ := fun i => kernel1 b i

def normalizedMatrix (s : Fin 21 → Bool) (t : Fin 7 → Bool) :
    Matrix (Fin 8 ⊕ Fin 1) (Fin 8 ⊕ Fin 1) ℚ :=
  augmented (fun i j => (template s i j : ℚ)) (qColumn t)

lemma pf6_cast (M : Matrix (Fin 6) (Fin 6) ℤ) :
    NormalizedPfaffian.pf6 (fun i j => (M i j : ℚ))=(pf6 M : ℚ) := by
  simp only [NormalizedPfaffian.pf6,pf6,Int.cast_sub,Int.cast_add,Int.cast_mul]

lemma pf8_cast (M : Matrix (Fin 8) (Fin 8) ℤ) :
    SignedRankSix.pf8 (fun i j => (M i j : ℚ))=((SignedRankSix.pf8 M : ℤ) : ℚ) := by
  simp only [SignedRankSix.pf8,SignedRankSix.pf6,
    Int.cast_sub,Int.cast_add,Int.cast_mul]

lemma qModel_pivot_det_ne (b : Fin 42) :
    ((qModel b).submatrix (pivots b) (pivots b)).det≠0 := by
  have ha : ∀ i j, (qModel b).submatrix (pivots b) (pivots b) i j =
      -(qModel b).submatrix (pivots b) (pivots b) j i := by
    intro i j
    change (models b (pivots b i) (pivots b j) : ℚ) =
      -(models b (pivots b j) (pivots b i) : ℚ)
    exact_mod_cast models_alternating b (pivots b i) (pivots b j)
  rw [NormalizedPfaffian.det_pf6_of_alternating _ ha]
  change NormalizedPfaffian.pf6
    (fun i j => (models b (pivots b i) (pivots b j) : ℚ))^2≠0
  rw [pf6_cast]
  apply pow_ne_zero
  exact_mod_cast pivot_pfaffian_nonzero b

lemma qKernel0_annihilates (b : Fin 42) (i : Fin 8) :
    (∑ j, qModel b i j*qKernel0 b j)=0 := by
  simp only [qModel,qKernel0]
  exact_mod_cast kernel0_annihilates b i

lemma qKernel1_annihilates (b : Fin 42) (i : Fin 8) :
    (∑ j, qModel b i j*qKernel1 b j)=0 := by
  simp only [qModel,qKernel1]
  exact_mod_cast kernel1_annihilates b i

lemma q_pairing_ne (b : Fin 42) (t : Fin 7 → Bool) :
    (∑ i, qColumn t i*qKernel0 b i)≠0 ∨ (∑ i, qColumn t i*qKernel1 b i)≠0 := by
  rcases no_kernel_compatible_extension b t with h | h
  · left
    have hh : (∑ i : Fin 8, (kernel0 b i : ℚ)*(extensionColumn t i : ℚ))≠0 := by
      exact_mod_cast h
    simpa only [qColumn,qKernel0,mul_comm] using hh
  · right
    have hh : (∑ i : Fin 8, (kernel1 b i : ℚ)*(extensionColumn t i : ℚ))≠0 := by
      exact_mod_cast h
    simpa only [qColumn,qKernel1,mul_comm] using hh

/-- Every choice of all 28 finite edge signs has augmented rank greater than
six. The infinity column is normalized; no restricted list of signings is
assumed complete in this theorem. -/
theorem normalized_rank_gt_six (s : Fin 21 → Bool) (t : Fin 7 → Bool) :
    6<(normalizedMatrix s t).rank := by
  by_contra! hle
  let M : Matrix (Fin 8) (Fin 8) ℚ := fun i j => template s i j
  have hr : M.rank≤6 := by
    have h := rank_submatrix_both_le (normalizedMatrix s t)
      (Sum.inl : Fin 8 → Fin 8 ⊕ Fin 1) (Sum.inl : Fin 8 → Fin 8 ⊕ Fin 1)
    exact h.trans hle
  have hd : M.det=0 := by
    by_contra hn
    have h := Matrix.rank_of_isUnit M
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hn))
    simp only [Fintype.card_fin] at h
    omega
  have ha : ∀ i j, M i j= -M j i := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [M,template]
  have hinf : ∀ i : Fin 7, M i.castSucc 7=1 := by
    intro i
    fin_cases i <;> simp [M,template]
  have hp : SignedRankSix.pf8 M=0 := by
    have hh := NormalizedPfaffian.det_pf8_of_normalized M ha hinf
    rw [hd] at hh
    exact eq_zero_of_pow_eq_zero hh.symm
  have hz : SignedRankSix.pf8 (template s)=0 := by
    change SignedRankSix.pf8 (fun i j => (template s i j : ℚ))=0 at hp
    rw [pf8_cast] at hp
    exact_mod_cast hp
  obtain ⟨b,hb⟩ := every_signing_classification s hz
  have hf : normalizedMatrix s t=augmented (qModel b) (qColumn t) := by
    simp only [normalizedMatrix,hb]
    rfl
  rw [hf] at hle
  rcases q_pairing_ne b t with h | h
  · have hg := rank_augmented_gt (qModel b) (pivots b) (qColumn t) (qKernel0 b)
      (qModel_pivot_det_ne b) (qKernel0_annihilates b) h
    omega
  · have hg := rank_augmented_gt (qModel b) (pivots b) (qColumn t) (qKernel1 b)
      (qModel_pivot_det_ne b) (qKernel1_annihilates b) h
    omega

#print axioms normalized_rank_gt_six
end Erdos213.AxisGlobalRankObstruction
