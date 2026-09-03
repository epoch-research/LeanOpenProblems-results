import Submission.EllipticTranslate

/-! A common positive real dilation is weaker than requiring every
rational squared length to be a rational square. This file gives exact
criteria using ratios, with an explicit nonzero anchor. -/
namespace Erdos213.CommonDistanceScale
noncomputable section
set_option maxHeartbeats 1000000

/-- Normalize by one positive length. No rationality of the original
length or of the dilation is assumed. -/
theorem lengths_iff {ι : Type*} (d : ι → ℝ) (q : ι → ℚ) (i₀ : ι)
    (hd : ∀ i, 0 ≤ d i) (h₀ : 0 < d i₀) (hq : ∀ i, d i^2 = (q i : ℝ)) :
    (∃ scale : ℝ, 0 < scale ∧ ∀ i, scale*d i ∈ Set.range ((↑) : ℚ → ℝ)) ↔
      ∀ i, IsSquare (q i/q i₀) := by
  have hratio (i : ι) : (d i/d i₀)^2 = ((q i/q i₀ : ℚ) : ℝ) := by
    push_cast
    rw [div_pow,hq,hq]
  constructor
  · rintro ⟨scale,hscale,h⟩ i
    obtain ⟨a,ha⟩ := h i
    obtain ⟨b,hb⟩ := h i₀
    have hrat : d i/d i₀ ∈ Set.range ((↑) : ℚ → ℝ) := by
      refine ⟨a/b,?_⟩
      push_cast
      rw [ha,hb]
      exact mul_div_mul_left _ _ (ne_of_gt hscale)
    exact (EllipticTranslate.rational_of_sq (div_nonneg (hd i) h₀.le) (hratio i)).mp hrat
  · intro h
    refine ⟨1/d i₀,one_div_pos.mpr h₀,?_⟩
    intro i
    rw [show (1/d i₀)*d i = d i/d i₀ by ring]
    exact (EllipticTranslate.rational_of_sq (div_nonneg (hd i) h₀.le) (hratio i)).mpr (h i)

lemma square_ratio_iff_product (a b : ℚ) (hb : b ≠ 0) :
    IsSquare (a/b) ↔ IsSquare (a*b) := by
  constructor
  · intro h
    convert h.mul (IsSquare.sq b) using 1
    field_simp
  · intro h
    convert h.div (IsSquare.sq b) using 1
    field_simp

/-- Equivalent product form: all rational squared lengths share a square
class. Zero lengths are harmless; only the anchor is required positive. -/
theorem lengths_iff_products {ι : Type*} (d : ι → ℝ) (q : ι → ℚ) (i₀ : ι)
    (hd : ∀ i, 0 ≤ d i) (h₀ : 0 < d i₀) (hq : ∀ i, d i^2 = (q i : ℝ)) :
    (∃ scale : ℝ, 0 < scale ∧ ∀ i, scale*d i ∈ Set.range ((↑) : ℚ → ℝ)) ↔
      ∀ i j, IsSquare (q i*q j) := by
  have hq₀ : q i₀ ≠ 0 := by
    intro h
    have hh := hq i₀
    rw [h,Rat.cast_zero] at hh
    nlinarith
  rw [lengths_iff d q i₀ hd h₀ hq]
  constructor
  · intro h i j
    have hh := ((h i).mul (h j)).mul (IsSquare.sq (q i₀))
    convert hh using 1
    field_simp
  · intro h i
    exact (square_ratio_iff_product _ _ hq₀).mpr (h i i₀)

/-- Rational nonzero square factors can be discarded before testing the
common-scale condition. This is the form needed for the elliptic offsets. -/
theorem factored_lengths_iff {ι : Type*} (d : ι → ℝ) (a f : ι → ℚ) (i₀ : ι)
    (hd : ∀ i, 0 ≤ d i) (h₀ : 0 < d i₀) (ha : ∀ i, a i ≠ 0)
    (hsq : ∀ i, d i^2 = ((a i^2*f i : ℚ) : ℝ)) :
    (∃ scale : ℝ, 0 < scale ∧ ∀ i, scale*d i ∈ Set.range ((↑) : ℚ → ℝ)) ↔
      ∀ i, IsSquare (f i/f i₀) := by
  rw [lengths_iff d (fun i => a i^2*f i) i₀ hd h₀ hsq]
  apply forall_congr'
  intro i
  rw [show a i^2*f i/(a i₀^2*f i₀) = (a i/a i₀)^2*(f i/f i₀) by
    rw [div_pow,mul_div_mul_comm]]
  exact EllipticTranslate.square_mul_sq_iff _ _ (div_ne_zero (ha i) (ha i₀))


/-- Metric bridge for a collection of nonvertical elliptic chords. The
remaining condition is common square class, not individual squareness. -/
theorem elliptic_edges_iff {ι : Type*} (A B s : ℚ) (u v r w : ι → ℚ) (i₀ : ι)
    (hs : EllipticTranslate.value A B s < 0)
    (hu : ∀ i, v i^2 = EllipticTranslate.value A B (u i))
    (hr : ∀ i, w i^2 = EllipticTranslate.value A B (r i))
    (hur : ∀ i, u i ≠ r i)
    (h₀ : 0 < dist (EllipticTranslate.point A B s (u i₀) (v i₀))
      (EllipticTranslate.point A B s (r i₀) (w i₀))) :
    (∃ scale : ℝ, 0 < scale ∧ ∀ i,
      scale*dist (EllipticTranslate.point A B s (u i) (v i))
        (EllipticTranslate.point A B s (r i) (w i)) ∈ Set.range ((↑) : ℚ → ℝ)) ↔
      ∀ i, IsSquare
        ((EllipticTranslate.sumX (u i) (v i) (r i) (w i)-EllipticTranslate.doubleX A B s)/
          (EllipticTranslate.sumX (u i₀) (v i₀) (r i₀) (w i₀)-EllipticTranslate.doubleX A B s)) := by
  have hus (i) := EllipticTranslate.on_curve_ne_source A B s (u i) (v i) hs (hu i)
  have hrs (i) := EllipticTranslate.on_curve_ne_source A B s (r i) (w i) hs (hr i)
  refine factored_lengths_iff
    (fun i => dist (EllipticTranslate.point A B s (u i) (v i))
      (EllipticTranslate.point A B s (r i) (w i)))
    (fun i => 2*(u i-r i)/((u i-s)*(r i-s)))
    (fun i => EllipticTranslate.sumX (u i) (v i) (r i) (w i)-EllipticTranslate.doubleX A B s)
    i₀ (fun _ => dist_nonneg) h₀ ?_ ?_
  · intro i
    exact div_ne_zero (mul_ne_zero (by norm_num) (sub_ne_zero.mpr (hur i)))
      (mul_ne_zero (sub_ne_zero.mpr (hus i)) (sub_ne_zero.mpr (hrs i)))
  · intro i
    rw [EllipticTranslate.point_dist_sq _ _ _ _ _ _ _ hs,
      EllipticTranslate.norm_sum_identity _ _ _ _ _ _ _ (hu i) (hr i)
        (ne_of_lt hs) (hus i) (hrs i) (hur i)]

/-- The square-class test depends only on the image of the profile index.
For the translated torsion coset that image is its restricted sumset. -/
lemma profile_image_iff {ι Γ : Type*} (index : ι → Γ) (f : Γ → ℚ) (i₀ : ι) :
    (∀ i, IsSquare (f (index i)/f (index i₀))) ↔
      (∀ g ∈ Set.range index, IsSquare (f g/f (index i₀))) := by
  constructor
  · rintro h _ ⟨i,rfl⟩
    exact h i
  · intro h i
    exact h _ ⟨i,rfl⟩

#print axioms lengths_iff
#print axioms lengths_iff_products
#print axioms factored_lengths_iff
#print axioms elliptic_edges_iff
#print axioms profile_image_iff
end
end Erdos213.CommonDistanceScale
