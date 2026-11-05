import FormalConjecturesUtil

/-!
# Clearing rational distances by a positive homothety

This file is independent of `Submission.Spec`. It does not assert the existence of
arbitrarily large rational-distance configurations. It proves that a *given finite*
rational-distance configuration can be scaled to an integral-distance configuration,
without changing its cardinality or its general-position properties.

The common denominator is a finite product of the denominators of rational distance
values, not of the coordinates of the points. Empty configurations are included.
-/

open EuclideanGeometry

namespace DistanceScaling

/-- The Euclidean plane used by the scaling results. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Homothety about the origin with real scale factor `c`. -/
def scale (c : ℝ) (p : Plane) : Plane := c • p

/- ## A finite product of denominators -/

/-- An explicit common denominator for a finite set of rational numbers. -/
def denominatorProduct (s : Finset ℚ) : ℕ := ∏ q ∈ s, q.den

/-- The product is positive, including when `s` is empty (when it is `1`). -/
theorem denominatorProduct_pos (s : Finset ℚ) : 0 < denominatorProduct s := by
  exact Finset.prod_pos fun q _ => q.den_pos

/-- Each denominator divides the common denominator. -/
theorem den_dvd_denominatorProduct {s : Finset ℚ} {q : ℚ} (hq : q ∈ s) :
    q.den ∣ denominatorProduct s :=
  Finset.dvd_prod_of_mem (fun r : ℚ => r.den) hq

/-- Multiplying a rational real number by its denominator gives its integer numerator. -/
theorem den_mul_ratCast (q : ℚ) : (q.den : ℝ) * (q : ℝ) = (q.num : ℝ) := by
  rw [Rat.cast_def, mul_div_cancel₀]
  exact_mod_cast q.den_nz

/-- Any natural-number multiple of a rational's denominator clears that denominator. -/
theorem mul_ratCast_mem_intCast_range {D : ℕ} (q : ℚ) (hD : q.den ∣ D) :
    (D : ℝ) * (q : ℝ) ∈ Set.range (Int.cast : ℤ → ℝ) := by
  obtain ⟨k, rfl⟩ := hD
  refine ⟨(k : ℤ) * q.num, ?_⟩
  push_cast
  rw [mul_comm (q.den : ℝ) (k : ℝ), mul_assoc, den_mul_ratCast]

/-- The explicit denominator product makes every member of `s` integral. -/
theorem denominatorProduct_clears {s : Finset ℚ} {q : ℚ} (hq : q ∈ s) :
    (denominatorProduct s : ℝ) * (q : ℝ) ∈ Set.range (Int.cast : ℤ → ℝ) :=
  mul_ratCast_mem_intCast_range q (den_dvd_denominatorProduct hq)

/-- A finite set of rational real numbers has a positive natural common denominator. -/
theorem finite_common_denominator {T : Set ℝ} (hT : T.Finite)
    (hRat : ∀ x ∈ T, x ∈ Set.range (Rat.cast : ℚ → ℝ)) :
    ∃ D : ℕ, 0 < D ∧ ∀ x ∈ T, (D : ℝ) * x ∈ Set.range (Int.cast : ℤ → ℝ) := by
  classical
  have hQ : ((Rat.cast : ℚ → ℝ) ⁻¹' T).Finite :=
    Set.Finite.preimage Rat.cast_injective.injOn hT
  refine ⟨denominatorProduct hQ.toFinset, denominatorProduct_pos _, ?_⟩
  intro x hx
  obtain ⟨q, rfl⟩ := hRat x hx
  exact denominatorProduct_clears (hQ.mem_toFinset.mpr hx)

/-- Rational distances on a finite metric configuration have a common denominator.
The conclusion includes diagonal pairs; the hypothesis only concerns distinct pairs. -/
theorem rational_distances_common_denominator {α : Type*} [PseudoMetricSpace α]
    {S : Set α} (hS : S.Finite)
    (hRat : S.Pairwise fun p q => dist p q ∈ Set.range (Rat.cast : ℚ → ℝ)) :
    ∃ D : ℕ, 0 < D ∧ ∀ p ∈ S, ∀ q ∈ S,
      (D : ℝ) * dist p q ∈ Set.range (Int.cast : ℤ → ℝ) := by
  let T : Set ℝ := (fun pq : α × α => dist pq.1 pq.2) '' (S ×ˢ S)
  have hT : T.Finite := (hS.prod hS).image _
  have hTRat : ∀ x ∈ T, x ∈ Set.range (Rat.cast : ℚ → ℝ) := by
    rintro x ⟨⟨p, q⟩, ⟨hp, hq⟩, rfl⟩
    by_cases hpq : p = q
    · subst q
      exact ⟨0, by simp⟩
    · exact hRat hp hq hpq
  obtain ⟨D, hD, hclear⟩ := finite_common_denominator hT hTRat
  refine ⟨D, hD, fun p hp q hq => hclear _ ?_⟩
  exact ⟨(p, q), ⟨hp, hq⟩, rfl⟩

/- ## Nonzero homotheties as mathlib affine equivalences -/

/-- The nonzero homothety, bundled as mathlib's affine equivalence. -/
noncomputable def homothetyEquiv (c : ℝ) (hc : c ≠ 0) : Plane ≃ᵃ[ℝ] Plane :=
  AffineEquiv.homothetyUnitsMulHom (0 : Plane) (Units.mk0 c hc)

@[simp]
theorem homothetyEquiv_apply (c : ℝ) (hc : c ≠ 0) (p : Plane) :
    homothetyEquiv c hc p = scale c p := by
  simp [homothetyEquiv, AffineEquiv.coe_homothetyUnitsMulHom_apply,
    AffineMap.homothety_apply, scale]

@[simp]
theorem homothetyEquiv_symm_apply (c : ℝ) (hc : c ≠ 0) (p : Plane) :
    (homothetyEquiv c hc).symm p = scale c⁻¹ p := by
  simp [homothetyEquiv, AffineEquiv.coe_homothetyUnitsMulHom_apply_symm,
    AffineMap.homothety_apply, scale]

/-- A nonzero homothety is injective. -/
theorem scale_injective {c : ℝ} (hc : c ≠ 0) : Function.Injective (scale c) := by
  intro p q hpq
  apply (homothetyEquiv c hc).injective
  simpa only [homothetyEquiv_apply] using hpq

/-- In particular, scaling by a positive natural number is injective. -/
theorem nat_scale_injective {D : ℕ} (hD : 0 < D) :
    Function.Injective (scale (D : ℝ)) :=
  scale_injective (by exact_mod_cast hD.ne')

/-- Reciprocal scaling undoes scaling on every set. -/
theorem inverse_scale_image {c : ℝ} (hc : c ≠ 0) (S : Set Plane) :
    scale c⁻¹ '' (scale c '' S) = S := by
  simp only [Set.image_image, scale, smul_smul, inv_mul_cancel₀ hc, one_smul,
    Set.image_id']

/-- Distance is multiplied by the nonnegative real scale factor. -/
theorem dist_scale {c : ℝ} (hc : 0 ≤ c) (p q : Plane) :
    dist (scale c p) (scale c q) = c * dist p q := by
  rw [scale, scale, dist_smul₀, Real.norm_of_nonneg hc]

/-- The distance scaling identity for natural-number homotheties. -/
theorem dist_nat_scale (D : ℕ) (p q : Plane) :
    dist (scale (D : ℝ) p) (scale (D : ℝ) q) = (D : ℝ) * dist p q :=
  dist_scale (Nat.cast_nonneg D) p q

/-- Scaling preserves finiteness, even with zero scale factor. -/
theorem finite_scale (c : ℝ) {S : Set Plane} (hS : S.Finite) :
    (scale c '' S).Finite := hS.image _

/-- Nonzero scaling preserves finiteness in both directions. -/
theorem finite_scale_iff {c : ℝ} (hc : c ≠ 0) (S : Set Plane) :
    (scale c '' S).Finite ↔ S.Finite :=
  Set.finite_image_iff (scale_injective hc).injOn

/-- Nonzero scaling preserves set cardinality; no finiteness hypothesis is needed. -/
theorem ncard_scale {c : ℝ} (hc : c ≠ 0) (S : Set Plane) :
    (scale c '' S).ncard = S.ncard :=
  Set.ncard_image_of_injective S (scale_injective hc)

/- ## Collinearity and fixed-cardinality subset properties -/

section Affine

variable {k V₁ P₁ V₂ P₂ : Type*} [DivisionRing k]
  [AddCommGroup V₁] [Module k V₁] [AddTorsor V₁ P₁]
  [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]

/-- An affine map sends a collinear set to a collinear set. -/
theorem collinear_image_affineMap (f : P₁ →ᵃ[k] P₂) {S : Set P₁}
    (hS : Collinear k S) : Collinear k (f '' S) := by
  obtain ⟨p₀, v, hv⟩ := (collinear_iff_exists_forall_eq_smul_vadd S).mp hS
  refine (collinear_iff_exists_forall_eq_smul_vadd (f '' S)).mpr ⟨f p₀, f.linear v, ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  obtain ⟨r, rfl⟩ := hv p hp
  exact ⟨r, by rw [f.map_vadd, f.linear.map_smul]⟩

/-- An affine equivalence preserves collinearity in both directions. -/
theorem collinear_image_affineEquiv_iff (e : P₁ ≃ᵃ[k] P₂) (S : Set P₁) :
    Collinear k (e '' S) ↔ Collinear k S := by
  constructor
  · intro h
    have h' := collinear_image_affineMap e.symm.toAffineMap h
    simpa only [AffineEquiv.coe_toAffineMap, Set.image_image,
      AffineEquiv.symm_apply_apply, Set.image_id'] using h'
  · exact collinear_image_affineMap e.toAffineMap

end Affine

/-- Nonzero scaling preserves collinearity of arbitrary sets in both directions. -/
theorem collinear_scale_iff {c : ℝ} (hc : c ≠ 0) (S : Set Plane) :
    Collinear ℝ (scale c '' S) ↔ Collinear ℝ S := by
  simpa only [homothetyEquiv_apply] using
    collinear_image_affineEquiv_iff (homothetyEquiv c hc) S

/-- Transfer a property of all `n`-element subsets through an equivalence.
This abstract lemma is independent of any particular geometric admissibility predicate. -/
theorem subset_property_image_equiv_iff {α : Type*} (e : α ≃ α)
    (P : Set α → Prop) (hP : ∀ T, P (e '' T) ↔ P T) (n : ℕ) (S : Set α) :
    (∀ T ⊆ e '' S, T.ncard = n → P T) ↔ (∀ T ⊆ S, T.ncard = n → P T) := by
  constructor
  · intro h T hTS hTcard
    apply (hP T).mp
    apply h (e '' T) (Set.image_mono hTS)
    simpa only [Set.ncard_image_of_injective T e.injective] using hTcard
  · intro h T hTS hTcard
    have hpre : e ⁻¹' T ⊆ S := by
      simpa only [e.preimage_image S] using (Set.preimage_mono (f := (e : α → α)) hTS)
    have himage : e '' (e ⁻¹' T) = T := Set.image_preimage_eq T e.surjective
    have hprecard : (e ⁻¹' T).ncard = n := by
      rw [← Set.ncard_image_of_injective (e ⁻¹' T) e.injective, himage]
      exact hTcard
    have hPT := (hP (e ⁻¹' T)).mpr (h (e ⁻¹' T) hpre hprecard)
    simpa only [himage] using hPT

/-- Nonzero homotheties preserve the exact `NonTrilinear` predicate. -/
theorem nonTrilinear_scale_iff {c : ℝ} (hc : c ≠ 0) (S : Set Plane) :
    NonTrilinear (scale c '' S) ↔ NonTrilinear S := by
  unfold NonTrilinear
  rw [Set.triplewise_set_pred_iff (P := fun T : Set Plane => ¬ Collinear ℝ T),
    Set.triplewise_set_pred_iff (P := fun T : Set Plane => ¬ Collinear ℝ T)]
  let e := homothetyEquiv c hc
  have hP : ∀ T : Set Plane, (¬ Collinear ℝ (e '' T)) ↔ ¬ Collinear ℝ T := by
    intro T
    exact not_congr (collinear_image_affineEquiv_iff e T)
  simpa only [e, AffineEquiv.coe_toEquiv, homothetyEquiv_apply] using
    subset_property_image_equiv_iff e.toEquiv (fun T => ¬ Collinear ℝ T) hP 3 S

/- ## Cospherical sets and general position -/

/-- Any real homothety sends a cospherical set to a cospherical set. -/
theorem cospherical_scale (c : ℝ) {S : Set Plane} (hS : Cospherical S) :
    Cospherical (scale c '' S) := by
  obtain ⟨center, radius, h⟩ := hS
  refine ⟨scale c center, ‖c‖ * radius, ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  rw [scale, scale, dist_smul₀, h p hp]

/-- Nonzero scaling preserves `Cospherical` in both directions. -/
theorem cospherical_scale_iff {c : ℝ} (hc : c ≠ 0) (S : Set Plane) :
    Cospherical (scale c '' S) ↔ Cospherical S := by
  constructor
  · intro h
    have h' := cospherical_scale c⁻¹ h
    simpa only [inverse_scale_image hc S] using h'
  · exact cospherical_scale c

/-- The condition that no four-element subset is cospherical is invariant under scaling.
The curried subset/cardinality hypotheses are equivalent to their conjunction. -/
theorem no_four_cospherical_scale_iff {c : ℝ} (hc : c ≠ 0) (S : Set Plane) :
    (∀ Q ⊆ scale c '' S, Q.ncard = 4 → ¬ Cospherical Q) ↔
      (∀ Q ⊆ S, Q.ncard = 4 → ¬ Cospherical Q) := by
  let e := homothetyEquiv c hc
  have hP : ∀ Q : Set Plane, (¬ Cospherical (e '' Q)) ↔ ¬ Cospherical Q := by
    intro Q
    simpa only [e, homothetyEquiv_apply] using not_congr (cospherical_scale_iff hc Q)
  simpa only [e, AffineEquiv.coe_toEquiv, homothetyEquiv_apply] using
    subset_property_image_equiv_iff e.toEquiv (fun Q => ¬ Cospherical Q) hP 4 S

/-- Positive (indeed, any nonzero) scaling preserves the imported plane general-position predicate. -/
theorem inGeneralPosition_scale_iff {c : ℝ} (hc : c ≠ 0) (S : Set Plane) :
    InGeneralPosition (scale c '' S) ↔ InGeneralPosition S := by
  exact and_congr (nonTrilinear_scale_iff hc S) (no_four_cospherical_scale_iff hc S)

/- ## Rational-distance configurations become integral-distance configurations -/

/-- A finite rational-distance configuration has a positive integral-distance scaling.
All pairs, including diagonal pairs, are covered by the conclusion. -/
theorem exists_integral_distance_scaling {S : Set Plane} (hS : S.Finite)
    (hRat : S.Pairwise fun p q => dist p q ∈ Set.range (Rat.cast : ℚ → ℝ)) :
    ∃ D : ℕ, 0 < D ∧ ∀ p ∈ S, ∀ q ∈ S,
      dist (scale (D : ℝ) p) (scale (D : ℝ) q) ∈ Set.range (Int.cast : ℤ → ℝ) := by
  obtain ⟨D, hD, hclear⟩ := rational_distances_common_denominator hS hRat
  refine ⟨D, hD, ?_⟩
  intro p hp q hq
  simpa only [dist_nat_scale] using hclear p hp q hq

/-- The full scaling infrastructure: finiteness, cardinality, non-trilinearity, and
absence of four cospherical points are preserved, while distances become integers.
No existence of the input configuration is asserted. -/
theorem exists_integral_scaling {S : Set Plane} (hS : S.Finite)
    (hRat : S.Pairwise fun p q => dist p q ∈ Set.range (Rat.cast : ℚ → ℝ)) :
    ∃ D : ℕ, 0 < D ∧
      (scale (D : ℝ) '' S).Finite ∧
      (scale (D : ℝ) '' S).ncard = S.ncard ∧
      (NonTrilinear (scale (D : ℝ) '' S) ↔ NonTrilinear S) ∧
      ((∀ Q ⊆ scale (D : ℝ) '' S, Q.ncard = 4 → ¬ Cospherical Q) ↔
        (∀ Q ⊆ S, Q.ncard = 4 → ¬ Cospherical Q)) ∧
      (scale (D : ℝ) '' S).Pairwise
        (fun p q => dist p q ∈ Set.range (Int.cast : ℤ → ℝ)) := by
  obtain ⟨D, hD, hdist⟩ := exists_integral_distance_scaling hS hRat
  have hDne : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  refine ⟨D, hD, finite_scale _ hS, ncard_scale hDne S,
    nonTrilinear_scale_iff hDne S, no_four_cospherical_scale_iff hDne S, ?_⟩
  rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ _
  exact hdist p hp q hq

/-- A version for any predicate invariant under positive real homotheties. -/
theorem exists_integral_scaling_preserving (P : Set Plane → Prop)
    (hP : ∀ c : ℝ, 0 < c → ∀ T : Set Plane, P (scale c '' T) ↔ P T)
    {S : Set Plane} (hS : S.Finite)
    (hRat : S.Pairwise fun p q => dist p q ∈ Set.range (Rat.cast : ℚ → ℝ))
    (hPS : P S) :
    ∃ D : ℕ, 0 < D ∧
      (scale (D : ℝ) '' S).Finite ∧
      (scale (D : ℝ) '' S).ncard = S.ncard ∧
      P (scale (D : ℝ) '' S) ∧
      (scale (D : ℝ) '' S).Pairwise
        (fun p q => dist p q ∈ Set.range (Int.cast : ℤ → ℝ)) := by
  obtain ⟨D, hD, hfin, hcard, _, _, hint⟩ := exists_integral_scaling hS hRat
  exact ⟨D, hD, hfin, hcard, (hP D (by exact_mod_cast hD) S).mpr hPS, hint⟩

/-- In particular, a given finite rational-distance set in general position can be
scaled to an integral-distance set of the same cardinality in general position. -/
theorem exists_integral_scaling_of_inGeneralPosition {S : Set Plane} (hS : S.Finite)
    (hRat : S.Pairwise fun p q => dist p q ∈ Set.range (Rat.cast : ℚ → ℝ))
    (hpos : InGeneralPosition S) :
    ∃ D : ℕ, 0 < D ∧
      (scale (D : ℝ) '' S).Finite ∧
      (scale (D : ℝ) '' S).ncard = S.ncard ∧
      InGeneralPosition (scale (D : ℝ) '' S) ∧
      (scale (D : ℝ) '' S).Pairwise
        (fun p q => dist p q ∈ Set.range (Int.cast : ℤ → ℝ)) := by
  apply exists_integral_scaling_preserving InGeneralPosition ?_ hS hRat hpos
  intro c hc T
  exact inGeneralPosition_scale_iff hc.ne' T

/-- A corollary with the exact conjunction-form geometric hypotheses:
no three collinear and no four cospherical. It only converts an already given set. -/
theorem exists_integral_scaling_admissible {S : Set Plane} (hS : S.Finite)
    (hRat : S.Pairwise fun p q => dist p q ∈ Set.range (Rat.cast : ℚ → ℝ))
    (hTri : NonTrilinear S)
    (hFour : ∀ Q : Set Plane, Q ⊆ S ∧ Q.ncard = 4 → ¬ Cospherical Q) :
    ∃ D : ℕ, 0 < D ∧
      (scale (D : ℝ) '' S).Finite ∧
      (scale (D : ℝ) '' S).ncard = S.ncard ∧
      NonTrilinear (scale (D : ℝ) '' S) ∧
      (∀ Q : Set Plane, Q ⊆ scale (D : ℝ) '' S ∧ Q.ncard = 4 → ¬ Cospherical Q) ∧
      (scale (D : ℝ) '' S).Pairwise
        (fun p q => dist p q ∈ Set.range (Int.cast : ℤ → ℝ)) := by
  obtain ⟨D, hD, hfin, hcard, htri, hfour, hint⟩ := exists_integral_scaling hS hRat
  refine ⟨D, hD, hfin, hcard, htri.mpr hTri, ?_, hint⟩
  intro Q hQ
  exact (hfour.mpr (fun T hTS hTcard => hFour T ⟨hTS, hTcard⟩)) Q hQ.1 hQ.2

end DistanceScaling

/- Kernel dependency audit for every declaration in this file. -/
#print axioms DistanceScaling.Plane
#print axioms DistanceScaling.scale
#print axioms DistanceScaling.denominatorProduct
#print axioms DistanceScaling.denominatorProduct_pos
#print axioms DistanceScaling.den_dvd_denominatorProduct
#print axioms DistanceScaling.den_mul_ratCast
#print axioms DistanceScaling.mul_ratCast_mem_intCast_range
#print axioms DistanceScaling.denominatorProduct_clears
#print axioms DistanceScaling.finite_common_denominator
#print axioms DistanceScaling.rational_distances_common_denominator
#print axioms DistanceScaling.homothetyEquiv
#print axioms DistanceScaling.homothetyEquiv_apply
#print axioms DistanceScaling.homothetyEquiv_symm_apply
#print axioms DistanceScaling.scale_injective
#print axioms DistanceScaling.nat_scale_injective
#print axioms DistanceScaling.inverse_scale_image
#print axioms DistanceScaling.dist_scale
#print axioms DistanceScaling.dist_nat_scale
#print axioms DistanceScaling.finite_scale
#print axioms DistanceScaling.finite_scale_iff
#print axioms DistanceScaling.ncard_scale
#print axioms DistanceScaling.collinear_image_affineMap
#print axioms DistanceScaling.collinear_image_affineEquiv_iff
#print axioms DistanceScaling.collinear_scale_iff
#print axioms DistanceScaling.subset_property_image_equiv_iff
#print axioms DistanceScaling.nonTrilinear_scale_iff
#print axioms DistanceScaling.cospherical_scale
#print axioms DistanceScaling.cospherical_scale_iff
#print axioms DistanceScaling.no_four_cospherical_scale_iff
#print axioms DistanceScaling.inGeneralPosition_scale_iff
#print axioms DistanceScaling.exists_integral_distance_scaling
#print axioms DistanceScaling.exists_integral_scaling
#print axioms DistanceScaling.exists_integral_scaling_preserving
#print axioms DistanceScaling.exists_integral_scaling_of_inGeneralPosition
#print axioms DistanceScaling.exists_integral_scaling_admissible
