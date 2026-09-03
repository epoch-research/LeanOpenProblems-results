import Submission.CyclicVarianceExplore

/-! Centered mixed-convolution variance on a finite abelian group. These
mean-square bounds do not assert pointwise flatness or give an infinite
integer construction. -/
namespace Erdos66CenteredMixedEnergy
open Erdos66MixedEnergy Erdos66CyclicVariance
open scoped Classical
variable {G : Type*} [AddCommGroup G] [Fintype G]

noncomputable def mixedMean (f g : G → ℝ) : ℝ :=
  (∑ x, f x) * (∑ x, g x) / Fintype.card G

noncomputable def centeredEnergy (f g : G → ℝ) : ℝ :=
  ∑ z, (conv f g z - mixedMean f g) ^ 2

noncomputable def centeredCorr (f : G → ℝ) (z : G) : ℝ :=
  corr f z - mixedMean f f

lemma card_pos : (0 : ℝ) < Fintype.card G := by
  exact_mod_cast Fintype.card_pos_iff.mpr (inferInstance : Nonempty G)

lemma sum_conv_mean (f g : G → ℝ) :
    (∑ z, conv f g z) = (Fintype.card G : ℝ) * mixedMean f g := by
  rw [sum_conv,mixedMean]
  field_simp [(card_pos (G := G)).ne']

lemma sum_corr_mean (f : G → ℝ) :
    (∑ z, corr f z) = (Fintype.card G : ℝ) * mixedMean f f := by
  rw [sum_corr,mixedMean]
  field_simp [(card_pos (G := G)).ne']

omit [AddCommGroup G] in
lemma sum_centered_product (u v : G → ℝ) (a b : ℝ)
    (hu : (∑ z, u z) = (Fintype.card G : ℝ)*a)
    (hv : (∑ z, v z) = (Fintype.card G : ℝ)*b) :
    (∑ z, (u z-a)*(v z-b)) = (∑ z, u z*v z) - (Fintype.card G : ℝ)*a*b := by
  simp_rw [sub_mul,mul_sub]
  simp only [Finset.sum_sub_distrib,
    Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [← Finset.sum_mul,← Finset.mul_sum,hu,hv]
  ring

lemma centeredEnergy_eq (f g : G → ℝ) :
    centeredEnergy f g = energy f g - (Fintype.card G : ℝ)*mixedMean f g ^ 2 := by
  unfold centeredEnergy energy
  simp_rw [pow_two]
  simpa only [mul_assoc] using sum_centered_product _ _ _ _ (sum_conv_mean f g) (sum_conv_mean f g)

/-- Centering commutes with the convolution/autocorrelation energy identity. -/
lemma centeredEnergy_eq_corr_inner (f g : G → ℝ) :
    centeredEnergy f g = ∑ z, centeredCorr f z * centeredCorr g z := by
  rw [centeredEnergy_eq]
  simp only [centeredCorr]
  rw [sum_centered_product _ _ _ _ (sum_corr_mean f) (sum_corr_mean g),
    ← energy_eq_corr_inner]
  have he : mixedMean f g ^ 2 = mixedMean f f * mixedMean g g := by
    unfold mixedMean
    ring
  rw [he]
  ring

lemma centeredEnergy_nonneg (f g : G → ℝ) : 0 ≤ centeredEnergy f g :=
  Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)

/-- The centered mixed energy is controlled by the two centered self energies,
not by the much larger uncentered energies. -/
theorem centered_mixed_energy_sq_le (f g : G → ℝ) :
    centeredEnergy f g ^ 2 ≤ centeredEnergy f f * centeredEnergy g g := by
  simp only [centeredEnergy_eq_corr_inner,← pow_two]
  exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (centeredCorr f) (centeredCorr g)

lemma centeredEnergy_minimizes (f g : G → ℝ) (a : ℝ) :
    centeredEnergy f g ≤ ∑ z, (conv f g z-a)^2 := by
  have hs := sum_conv_mean f g
  have he : (∑ z, (conv f g z-a)^2) =
      centeredEnergy f g + (Fintype.card G : ℝ)*(mixedMean f g-a)^2 := by
    rw [centeredEnergy_eq]
    simp_rw [sub_sq]
    simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.sum_const,
      Finset.card_univ,nsmul_eq_mul,energy]
    have hm : (∑ z, 2*conv f g z*a) = 2*a*(∑ z, conv f g z) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z hz
      ring
    rw [hm,hs]
    ring
  rw [he]
  exact le_add_of_nonneg_right (mul_nonneg (card_pos (G := G)).le (sq_nonneg _))

lemma self_centeredEnergy_le (f : G → ℝ) (a E : ℝ) (hE : 0 ≤ E)
    (hf : ∀ z, |conv f f z-a| ≤ E) :
    centeredEnergy f f ≤ (Fintype.card G : ℝ)*E^2 := by
  apply (centeredEnergy_minimizes f f a).trans
  calc
    _ ≤ ∑ _z : G, E^2 := by
      apply Finset.sum_le_sum
      intro z hz
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hE).mpr (hf z)
    _ = _ := by simp

/-- Uniform self-errors around arbitrary centers control mixed mean-square
error around the true mixed mean. -/
theorem mixed_centeredEnergy_le (f g : G → ℝ) (a b E F : ℝ)
    (hE : 0 ≤ E) (hF : 0 ≤ F)
    (hf : ∀ z, |conv f f z-a| ≤ E) (hg : ∀ z, |conv g g z-b| ≤ F) :
    centeredEnergy f g ≤ (Fintype.card G : ℝ)*E*F := by
  have hf' := self_centeredEnergy_le f a E hE hf
  have hg' := self_centeredEnergy_le g b F hF hg
  have hm := mul_le_mul hf' hg' (centeredEnergy_nonneg g g)
    (mul_nonneg (card_pos (G := G)).le (sq_nonneg E))
  have hcs := centered_mixed_energy_sq_le f g
  have hnon : 0 ≤ (Fintype.card G : ℝ)*E*F := by positivity
  have hnon' := centeredEnergy_nonneg f g
  nlinarith [sq_nonneg ((Fintype.card G : ℝ)*E*F - centeredEnergy f g)]

/-- A denominator-free bound for the exceptional mixed residues. -/
theorem bad_residue_mass_le (f g : G → ℝ) (a b E F δ : ℝ)
    (hE : 0 ≤ E) (hF : 0 ≤ F) (hδ : 0 ≤ δ)
    (hf : ∀ z, |conv f f z-a| ≤ E) (hg : ∀ z, |conv g g z-b| ≤ F) :
    (((Finset.univ.filter (fun z ↦ δ < |conv f g z-mixedMean f g|)).card : ℝ)*δ^2) ≤
      (Fintype.card G : ℝ)*E*F := by
  let S := Finset.univ.filter (fun z ↦ δ < |conv f g z-mixedMean f g|)
  have hlow : (S.card : ℝ)*δ^2 ≤ ∑ z ∈ S, (conv f g z-mixedMean f g)^2 := by
    calc
      _ = ∑ _z ∈ S, δ^2 := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro z hz
        have hz' := (Finset.mem_filter.mp hz).2
        simpa only [sq_abs] using (sq_le_sq₀ hδ (abs_nonneg _)).mpr hz'.le
  have hu : (∑ z ∈ S, (conv f g z-mixedMean f g)^2) ≤ centeredEnergy f g := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun z hz hz' ↦ sq_nonneg _)
  exact (hlow.trans hu).trans (mixed_centeredEnergy_le f g a b E F hE hF hf hg)

lemma conv_indicators (B C : Finset G) (z : G) :
    conv (indicator B) (indicator C) z = ((B.filter (fun a ↦ z-a ∈ C)).card : ℝ) := by
  simp [conv,indicator,← Finset.sum_filter]
  congr 1
  ext x
  simp only [Finset.mem_inter,Finset.mem_filter,Finset.mem_univ,true_and]
  tauto

/-- For actual finite sets, the mixed center is `|B|*|C|/|G|`. -/
theorem indicator_bad_residue_mass_le (B C : Finset G) (a b E F δ : ℝ)
    (hE : 0 ≤ E) (hF : 0 ≤ F) (hδ : 0 ≤ δ)
    (hB : ∀ z : G, |(((B.filter (fun x ↦ z-x ∈ B)).card : ℝ)-a)| ≤ E)
    (hC : ∀ z : G, |(((C.filter (fun x ↦ z-x ∈ C)).card : ℝ)-b)| ≤ F) :
    (((Finset.univ.filter (fun z ↦ δ <
      |(((B.filter (fun x ↦ z-x ∈ C)).card : ℝ) -
        (B.card : ℝ)*C.card/Fintype.card G)|)).card : ℝ)*δ^2) ≤
      (Fintype.card G : ℝ)*E*F := by
  simpa only [conv_indicators,mixedMean,sum_indicator] using
    bad_residue_mass_le (indicator B) (indicator C) a b E F δ hE hF hδ
      (by simpa only [conv_indicators] using hB) (by simpa only [conv_indicators] using hC)

/-- A sparse template has a square-root-sized uniform self-error. This is a
limitation on the preceding Chebyshev certificate, not a lower bound on the
actual number of exceptional mixed residues. -/
lemma sparse_self_error_floor (B : Finset G) (μ E : ℝ)
    (hμ : (Fintype.card G : ℝ)*μ = (B.card : ℝ)^2)
    (hsparse : (2 : ℝ)*B.card ≤ Fintype.card G) (hE : 0 ≤ E)
    (hB : ∀ z : G, |(((B.filter (fun x ↦ z-x ∈ B)).card : ℝ)-μ)| ≤ E) :
    μ ≤ 4*E^2 := by
  have hh := uniform_error_floor B μ E hμ hE hB
  let M : ℝ := Fintype.card G
  let m : ℝ := B.card
  have hM : 0 < M := card_pos
  have hm : 0 ≤ m := Nat.cast_nonneg _
  change m^2*(M-m)^2 ≤ M^2*(M-1)*E^2 at hh
  change M*μ = m^2 at hμ
  change 2*m ≤ M at hsparse
  have hsq : M^2 ≤ 4*(M-m)^2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hsq (sq_nonneg m)
  have hμ0 : 0 ≤ μ := by nlinarith [sq_nonneg m]
  have hupper : M^3*μ ≤ M^3*(4*E^2) := by
    nlinarith [mul_nonneg (sq_nonneg M) (sq_nonneg E)]
  exact (mul_le_mul_iff_right₀ (pow_pos hM 3)).mp hupper

/-- The numerical Chebyshev certificate coming from a common uniform error
cannot be made smaller than this solely by improving that error. This does
not say that the actual exceptional set has this cardinality. -/
theorem chebyshev_certificate_floor (B : Finset G) (μ E δ : ℝ)
    (hμpos : 0 < μ) (hδ : 0 < δ)
    (hμ : (Fintype.card G : ℝ)*μ = (B.card : ℝ)^2)
    (hsparse : (2 : ℝ)*B.card ≤ Fintype.card G) (hE : 0 ≤ E)
    (hB : ∀ z : G, |(((B.filter (fun x ↦ z-x ∈ B)).card : ℝ)-μ)| ≤ E) :
    (Fintype.card G : ℝ)/(4*δ^2*μ) ≤
      (Fintype.card G : ℝ)*E^2/(δ^2*μ^2) := by
  have he := sparse_self_error_floor B μ E hμ hsparse hE hB
  calc
    _ = ((Fintype.card G : ℝ)/(4*δ^2*μ^2))*μ := by
      field_simp [hμpos.ne',hδ.ne']
    _ ≤ ((Fintype.card G : ℝ)/(4*δ^2*μ^2))*(4*E^2) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by ring

end Erdos66CenteredMixedEnergy
