import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! A conditional reciprocal-star extension rule. No existence of the two
additional rational norms, and no general-position assertion, is made here. -/
namespace Erdos213.ReciprocalStar

def RationalNorm (z : ℂ) : Prop := ∃ q : ℚ, (q : ℝ) = ‖z‖

lemma RationalNorm.mul {z w : ℂ} (hz : RationalNorm z) (hw : RationalNorm w) :
    RationalNorm (z*w) := by
  obtain ⟨q,hq⟩ := hz
  obtain ⟨r,hr⟩ := hw
  exact ⟨q*r, by simp [hq, hr]⟩

lemma RationalNorm.div {z w : ℂ} (hz : RationalNorm z) (hw : RationalNorm w) :
    RationalNorm (z/w) := by
  obtain ⟨q,hq⟩ := hz
  obtain ⟨r,hr⟩ := hw
  exact ⟨q/r, by simp [hq, hr]⟩

@[simp] lemma rationalNorm_neg_iff (z : ℂ) : RationalNorm (-z) ↔ RationalNorm z := by
  simp [RationalNorm]

lemma rationalNorm_sub_rev {z w : ℂ} (h : RationalNorm (z-w)) :
    RationalNorm (w-z) := by
  simpa only [neg_sub, rationalNorm_neg_iff] using
    (rationalNorm_neg_iff (z-w)).mpr h

/-- Both cross-distances between antipodal pairs are rational. -/
def Compatible (z w : ℂ) : Prop := RationalNorm (z-w) ∧ RationalNorm (z+w)

lemma Compatible.symm {z w : ℂ} (h : Compatible z w) : Compatible w z :=
  ⟨rationalNorm_sub_rev h.1, by simpa only [add_comm] using h.2⟩

noncomputable def extension (a b c : ℂ) : ℂ := b*c/a

lemma extension_sub_first (a b c : ℂ) (ha : a ≠ 0) :
    extension a b c-a=(b*c-a^2)/a := by
  unfold extension
  field_simp

lemma extension_add_first (a b c : ℂ) (ha : a ≠ 0) :
    extension a b c+a=(b*c+a^2)/a := by
  unfold extension
  field_simp

lemma extension_sub_second (a b c : ℂ) (ha : a ≠ 0) :
    extension a b c-b=b*(c-a)/a := by
  unfold extension
  field_simp

lemma extension_add_second (a b c : ℂ) (ha : a ≠ 0) :
    extension a b c+b=b*(c+a)/a := by
  unfold extension
  field_simp

lemma extension_sub_third (a b c : ℂ) (ha : a ≠ 0) :
    extension a b c-c=c*(b-a)/a := by
  unfold extension
  field_simp

lemma extension_add_third (a b c : ℂ) (ha : a ≠ 0) :
    extension a b c+c=c*(b+a)/a := by
  unfold extension
  field_simp

lemma extension_automatic {a b c : ℂ} (ha : a ≠ 0)
    (hNa : RationalNorm a) (hNb : RationalNorm b) (hNc : RationalNorm c)
    (hab : Compatible a b) (hac : Compatible a c) :
    RationalNorm (extension a b c) ∧
      Compatible (extension a b c) b ∧ Compatible (extension a b c) c := by
  refine ⟨(hNb.mul hNc).div hNa, ?_, ?_⟩
  · constructor
    · rw [extension_sub_second a b c ha]
      exact (hNb.mul hac.symm.1).div hNa
    · rw [extension_add_second a b c ha]
      exact (hNb.mul hac.symm.2).div hNa
  · constructor
    · rw [extension_sub_third a b c ha]
      exact (hNc.mul hab.symm.1).div hNa
    · rw [extension_add_third a b c ha]
      exact (hNc.mul hab.symm.2).div hNa

lemma extension_first_iff {a b c : ℂ} (ha : a ≠ 0) (hNa : RationalNorm a) :
    Compatible (extension a b c) a ↔
      RationalNorm (b*c-a^2) ∧ RationalNorm (b*c+a^2) := by
  constructor
  · rintro ⟨hm,hp⟩
    have hm' := hm.mul hNa
    have hp' := hp.mul hNa
    rw [extension_sub_first a b c ha, div_mul_cancel₀ _ ha] at hm'
    rw [extension_add_first a b c ha, div_mul_cancel₀ _ ha] at hp'
    exact ⟨hm',hp'⟩
  · rintro ⟨hm,hp⟩
    constructor
    · rw [extension_sub_first a b c ha]
      exact hm.div hNa
    · rw [extension_add_first a b c ha]
      exact hp.div hNa

/-- Under the old radius and cross-distance conditions, precisely two new
rational norms remain. This is an equivalence, not an existence theorem. -/
theorem extension_criterion {a b c : ℂ} (ha : a ≠ 0)
    (hNa : RationalNorm a) (hNb : RationalNorm b) (hNc : RationalNorm c)
    (hab : Compatible a b) (hac : Compatible a c) :
    (RationalNorm (extension a b c) ∧ Compatible (extension a b c) a ∧
      Compatible (extension a b c) b ∧ Compatible (extension a b c) c) ↔
      RationalNorm (b*c-a^2) ∧ RationalNorm (b*c+a^2) := by
  constructor
  · intro h
    exact (extension_first_iff ha hNa).mp h.2.1
  · intro h
    obtain ⟨hd,hdb,hdc⟩ := extension_automatic ha hNa hNb hNc hab hac
    exact ⟨hd,(extension_first_iff ha hNa).mpr h,hdb,hdc⟩

#print axioms extension_automatic
#print axioms extension_first_iff
#print axioms extension_criterion

end Erdos213.ReciprocalStar
