import Submission.LambertCyclicCombinationLowerBound

/-! Nonsingularity of late raw-error Hankel blocks. This is not an
integral-boundary or irrationality statement. -/

namespace LambertRawHankelNonsingular

open LambertUniformRawNonvanishing LambertCyclicCombinationLowerBound

noncomputable section

variable (d : ℕ) [NeZero d]

def rawHankel (H : ℕ) : Matrix (ZMod d) (ZMod d) ℝ :=
  fun i j => rawTail (d-2) (H+i.val+j.val)

lemma mulVec_eq_zero (H : ℕ) (hd : 12 ≤ d)
    (hH : (d+1)*(3*(d.log2+1)+130) ≤ H) (w : ZMod d → ℝ)
    (hw : (rawHankel d H).mulVec w = 0) : w = 0 := by
  by_contra hne
  obtain ⟨n, hn, hnu, hdetect⟩ := raw_combination_explicit_window d H hd hH w hne
  let i : ZMod d := (n-H : ℕ)
  have hval : i.val = n-H := ZMod.val_natCast_of_lt (by omega)
  have he := congrFun hw i
  simp only [Matrix.mulVec, dotProduct, rawHankel, Pi.zero_apply, hval] at he
  have hn' : H+(n-H)=n := by omega
  simp only [hn'] at he
  apply hdetect
  simpa only [mul_comm] using he

lemma mulVec_injective (H : ℕ) (hd : 12 ≤ d)
    (hH : (d+1)*(3*(d.log2+1)+130) ≤ H) :
    Function.Injective (rawHankel d H).mulVec := by
  intro u v huv
  apply sub_eq_zero.mp
  apply mulVec_eq_zero d H hd hH
  rw [Matrix.mulVec_sub, huv, sub_self]

theorem rawHankel_isUnit (H : ℕ) (hd : 12 ≤ d)
    (hH : (d+1)*(3*(d.log2+1)+130) ≤ H) :
    IsUnit (rawHankel d H) :=
  Matrix.mulVec_injective_iff_isUnit.mp (mulVec_injective d H hd hH)

theorem rawHankel_det_ne_zero (H : ℕ) (hd : 12 ≤ d)
    (hH : (d+1)*(3*(d.log2+1)+130) ≤ H) :
    (rawHankel d H).det ≠ 0 := by
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det (rawHankel d H)).mp (rawHankel_isUnit d H hd hH))

end
end LambertRawHankelNonsingular

#print axioms LambertRawHankelNonsingular.rawHankel_isUnit
#print axioms LambertRawHankelNonsingular.rawHankel_det_ne_zero
