import Submission.WitnessResidueProjectionExplore

/-! At a fixed sum target, specifying one endpoint residue also specifies
the other. Thus the projection estimates are joint pair-count estimates. -/
namespace Erdos66ResiduePairIdentity
open Erdos66NaturalResidueProjection Erdos66ResidueSeries
open scoped Classical
open AdditiveCombinatorics
set_option maxHeartbeats 1800000
variable (m : ℕ) [NeZero m]

lemma residue_pair_eq (f : ℕ → ℝ) (i j : ZMod m) (n : ℕ) :
    sumConv (residueTerm m f i) (residueTerm m f j) n=
      if i+j=(n : ZMod m) then sumConv f (residueTerm m f j) n else 0 := by
  have hp (ab : ℕ×ℕ) (hab : ab∈Finset.antidiagonal n) :
      residueTerm m f i ab.1*residueTerm m f j ab.2=
        if i+j=(n : ZMod m) then f ab.1*residueTerm m f j ab.2 else 0 := by
    have hsum : (ab.1 : ZMod m)+(ab.2 : ZMod m)=(n : ZMod m) := by
      rw [← Nat.cast_add,Finset.mem_antidiagonal.mp hab]
    by_cases hj : (ab.2 : ZMod m)=j
    · have he : (ab.1 : ZMod m)=i ↔ i+j=(n : ZMod m) := by
        rw [← hsum,hj]
        constructor
        · intro hi; rw [hi]
        · intro hi; exact add_right_cancel hi.symm
      simp only [residueTerm,if_pos hj,he,ite_mul,zero_mul]
    · simp only [residueTerm,if_neg hj,mul_zero,ite_self]
  unfold sumConv
  by_cases h : i+j=(n : ZMod m)
  · rw [if_pos h]
    exact Finset.sum_congr rfl (fun ab hab ↦ by simpa only [if_pos h] using hp ab hab)
  · rw [if_neg h]
    exact Finset.sum_eq_zero (fun ab hab ↦ by simpa only [if_neg h] using hp ab hab)

noncomputable def pairError (f : ℕ → ℝ) (i j : ZMod m) (n : ℕ) : ℝ :=
  sumConv (residueTerm m f i) (residueTerm m f j) n-
    if i+j=(n : ZMod m) then sumConv f f n/m else 0

lemma pairError_eq (f : ℕ → ℝ) (i j : ZMod m) (n : ℕ) :
    pairError m f i j n=if i+j=(n : ZMod m) then projectionError m f j n else 0 := by
  rw [pairError,residue_pair_eq]
  split_ifs <;> simp only [projectionError,sub_self]

lemma sum_pairError_square (f : ℕ → ℝ) (j : ZMod m) (n : ℕ) :
    (∑ i : ZMod m, pairError m f i j n^2)=projectionError m f j n^2 := by
  have he (i : ZMod m) : i+j=(n : ZMod m) ↔ i=(n : ZMod m)-j :=
    eq_sub_iff_add_eq.symm
  simp only [pairError_eq,he,ite_pow,zero_pow (by decide : 2≠0)]
  simp

end Erdos66ResiduePairIdentity
