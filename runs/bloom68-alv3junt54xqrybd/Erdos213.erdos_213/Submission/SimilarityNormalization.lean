import Submission.DistanceScaling
import Submission.QuadraticNormalForm
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-!
# Similarity normalization of a given rational-distance configuration

Two distinct anchors can be sent to `0` and `QuadraticNormalForm.unitPoint`
by a bijective similarity of the whole Euclidean plane. The similarity is a
translation, followed by reflection in the perpendicular bisector subspace
of two equal-norm vectors, followed by a positive homothety. Its distance
factor is the reciprocal of the anchor distance, hence is rational when the
anchor distance is rational.

Finiteness, set cardinality, nontrilinearity, and the absence of four
cospherical points are invariant. Combining this normalization with the clean
`QuadraticNormalForm` results gives a common positive rational radicand for
the coordinates of an already given rational-distance configuration in
general position with at least three points.

This is a structural auxiliary result. It neither constructs arbitrary-size
configurations nor settles an existence conjecture. The specification module
is not imported.
-/

open EuclideanGeometry

namespace SimilarityNormalization

/-- The Euclidean plane, with its Euclidean rather than sup metric. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/- ## A reflection and a translated isometry -/

/-- The normalized second anchor has norm one. -/
@[simp]
theorem norm_unitPoint : ‖QuadraticNormalForm.unitPoint‖ = 1 := by
  simp [EuclideanSpace.norm_eq, Fin.sum_univ_two, QuadraticNormalForm.unitPoint]

/-- Reflection in the orthogonal complement of the difference of the two
vectors `B - A` and `dist A B • unitPoint`. Their equal norms ensure that the
first vector is sent to the second, even if the vectors already coincide. -/
noncomputable def anchorReflection (A B : Plane) : Plane ≃ₗᵢ[ℝ] Plane :=
  Submodule.reflection (ℝ ∙ ((B - A) - dist A B • QuadraticNormalForm.unitPoint))ᗮ

@[simp]
theorem anchorReflection_sub (A B : Plane) :
    anchorReflection A B (B - A) = dist A B • QuadraticNormalForm.unitPoint := by
  apply Submodule.reflection_sub
  calc
    ‖B - A‖ = dist B A := (dist_eq_norm B A).symm
    _ = dist A B := dist_comm B A
    _ = ‖dist A B • QuadraticNormalForm.unitPoint‖ := by
      rw [norm_smul, Real.norm_of_nonneg dist_nonneg, norm_unitPoint, mul_one]

/-- First translate `A` to the origin, then apply the anchor reflection. -/
noncomputable def anchorIsometry (A B : Plane) : Plane ≃ᵃⁱ[ℝ] Plane :=
  (AffineIsometryEquiv.vaddConst ℝ A).symm.trans
    (anchorReflection A B).toAffineIsometryEquiv

@[simp]
theorem anchorIsometry_apply (A B p : Plane) :
    anchorIsometry A B p = anchorReflection A B (p - A) := rfl

/- ## The nonzero homothety and its metric identity -/

/-- A bijective similarity sending the distinct anchors to `0` and `unitPoint`.
Bundling it as an affine equivalence also makes its collinearity API available. -/
noncomputable def normalizationAffineEquiv (A B : Plane) (hAB : A ≠ B) :
    Plane ≃ᵃ[ℝ] Plane :=
  (anchorIsometry A B).toAffineEquiv.trans
    (DistanceScaling.homothetyEquiv (dist A B)⁻¹
      (inv_ne_zero (dist_ne_zero.mpr hAB)))

@[simp]
theorem normalizationAffineEquiv_apply (A B : Plane) (hAB : A ≠ B) (p : Plane) :
    normalizationAffineEquiv A B hAB p =
      (dist A B)⁻¹ • anchorReflection A B (p - A) := by
  simp [normalizationAffineEquiv, DistanceScaling.scale]

/-- The normalization is a bijection of the entire plane, not merely of the set. -/
theorem normalizationAffineEquiv_bijective (A B : Plane) (hAB : A ≠ B) :
    Function.Bijective (normalizationAffineEquiv A B hAB) :=
  (normalizationAffineEquiv A B hAB).bijective

@[simp]
theorem normalizationAffineEquiv_left (A B : Plane) (hAB : A ≠ B) :
    normalizationAffineEquiv A B hAB A = 0 := by
  simp

@[simp]
theorem normalizationAffineEquiv_right (A B : Plane) (hAB : A ≠ B) :
    normalizationAffineEquiv A B hAB B = QuadraticNormalForm.unitPoint := by
  simp [smul_smul, dist_ne_zero.mpr hAB]

/-- Every distance, including distances outside the configuration, is divided
by the strictly positive anchor distance. -/
theorem dist_normalizationAffineEquiv (A B : Plane) (hAB : A ≠ B) (p q : Plane) :
    dist (normalizationAffineEquiv A B hAB p) (normalizationAffineEquiv A B hAB q) =
      dist p q / dist A B := by
  simp only [normalizationAffineEquiv, AffineEquiv.trans_apply,
    DistanceScaling.homothetyEquiv_apply, AffineIsometryEquiv.coe_toAffineEquiv]
  rw [DistanceScaling.dist_scale (inv_nonneg.mpr dist_nonneg),
    (anchorIsometry A B).dist_map, div_eq_mul_inv, mul_comm]

/- ## Geometric invariance -/

/-- Finiteness is preserved in both directions. -/
theorem finite_normalization_iff (A B : Plane) (hAB : A ≠ B) (S : Set Plane) :
    (normalizationAffineEquiv A B hAB '' S).Finite ↔ S.Finite :=
  Set.finite_image_iff (normalizationAffineEquiv A B hAB).injective.injOn

/-- Set cardinality is preserved without a finiteness assumption. -/
theorem ncard_normalization (A B : Plane) (hAB : A ≠ B) (S : Set Plane) :
    (normalizationAffineEquiv A B hAB '' S).ncard = S.ncard :=
  Set.ncard_image_of_injective S (normalizationAffineEquiv A B hAB).injective

/-- Collinearity is invariant because the similarity is an affine equivalence. -/
theorem collinear_normalization_iff (A B : Plane) (hAB : A ≠ B) (S : Set Plane) :
    Collinear ℝ (normalizationAffineEquiv A B hAB '' S) ↔ Collinear ℝ S :=
  DistanceScaling.collinear_image_affineEquiv_iff
    (normalizationAffineEquiv A B hAB) S

/-- In the inverse direction, pull a circle center back through the bijection
and multiply its radius by the anchor distance. No sign assumption on the
witness radius or finiteness of the set is needed. -/
theorem cospherical_normalization_iff (A B : Plane) (hAB : A ≠ B) (S : Set Plane) :
    Cospherical (normalizationAffineEquiv A B hAB '' S) ↔ Cospherical S := by
  let e := normalizationAffineEquiv A B hAB
  constructor
  · rintro ⟨center, radius, h⟩
    refine ⟨e.symm center, radius * dist A B, ?_⟩
    intro p hp
    have hd := h (e p) (Set.mem_image_of_mem e hp)
    rw [← e.apply_symm_apply center, dist_normalizationAffineEquiv] at hd
    exact (div_eq_iff (dist_ne_zero.mpr hAB)).mp hd
  · rintro ⟨center, radius, h⟩
    refine ⟨e center, radius / dist A B, ?_⟩
    rintro _ ⟨p, hp, rfl⟩
    rw [dist_normalizationAffineEquiv, h p hp]

/-- The exact imported `NonTrilinear` predicate is invariant. -/
theorem nonTrilinear_normalization_iff (A B : Plane) (hAB : A ≠ B) (S : Set Plane) :
    NonTrilinear (normalizationAffineEquiv A B hAB '' S) ↔ NonTrilinear S := by
  unfold NonTrilinear
  rw [Set.triplewise_set_pred_iff (P := fun T : Set Plane => ¬ Collinear ℝ T),
    Set.triplewise_set_pred_iff (P := fun T : Set Plane => ¬ Collinear ℝ T)]
  let e := normalizationAffineEquiv A B hAB
  have hP : ∀ T : Set Plane, (¬ Collinear ℝ (e '' T)) ↔ ¬ Collinear ℝ T := by
    intro T
    exact not_congr (collinear_normalization_iff A B hAB T)
  simpa only [e, AffineEquiv.coe_toEquiv] using
    DistanceScaling.subset_property_image_equiv_iff e.toEquiv
      (fun T => ¬ Collinear ℝ T) hP 3 S

/-- The no-four-cospherical condition is invariant for arbitrary subsets. -/
theorem no_four_cospherical_normalization_iff
    (A B : Plane) (hAB : A ≠ B) (S : Set Plane) :
    (∀ Q ⊆ normalizationAffineEquiv A B hAB '' S, Q.ncard = 4 → ¬ Cospherical Q) ↔
      (∀ Q ⊆ S, Q.ncard = 4 → ¬ Cospherical Q) := by
  let e := normalizationAffineEquiv A B hAB
  have hP : ∀ Q : Set Plane, (¬ Cospherical (e '' Q)) ↔ ¬ Cospherical Q := by
    intro Q
    exact not_congr (cospherical_normalization_iff A B hAB Q)
  simpa only [e, AffineEquiv.coe_toEquiv] using
    DistanceScaling.subset_property_image_equiv_iff e.toEquiv
      (fun Q => ¬ Cospherical Q) hP 4 S

/-- The imported general-position predicate is invariant. -/
theorem inGeneralPosition_normalization_iff
    (A B : Plane) (hAB : A ≠ B) (S : Set Plane) :
    InGeneralPosition (normalizationAffineEquiv A B hAB '' S) ↔ InGeneralPosition S :=
  and_congr (nonTrilinear_normalization_iff A B hAB S)
    (no_four_cospherical_normalization_iff A B hAB S)

/- ## Rational distances and a positive rational similarity factor -/

/-- Rationality of the anchor distance makes rationality of every distance
invariant under normalization. The inverse implication multiplies by the
nonzero anchor distance, and the forward implication casts rational division. -/
theorem rational_dist_normalization_iff (A B : Plane) (hAB : A ≠ B)
    (hAnchor : dist A B ∈ Set.range (Rat.cast : ℚ → ℝ)) (p q : Plane) :
    dist (normalizationAffineEquiv A B hAB p) (normalizationAffineEquiv A B hAB q)
        ∈ Set.range (Rat.cast : ℚ → ℝ) ↔
      dist p q ∈ Set.range (Rat.cast : ℚ → ℝ) := by
  obtain ⟨d, hd⟩ := hAnchor
  have hdne : d ≠ 0 := by
    have hdne_real : (d : ℝ) ≠ 0 := by
      rw [hd]
      exact dist_ne_zero.mpr hAB
    exact_mod_cast hdne_real
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨r * d, ?_⟩
    rw [Rat.cast_mul, hr, dist_normalizationAffineEquiv, ← hd,
      div_mul_cancel₀ _ (by exact_mod_cast hdne)]
  · rintro ⟨r, hr⟩
    refine ⟨r / d, ?_⟩
    rw [Rat.cast_div, hr, hd, dist_normalizationAffineEquiv]

/-- Pairwise rational-distance configurations are preserved in both directions
whenever the anchor distance is rational. -/
theorem rational_distances_normalization_iff (A B : Plane) (hAB : A ≠ B)
    (hAnchor : dist A B ∈ Set.range (Rat.cast : ℚ → ℝ)) (S : Set Plane) :
    (normalizationAffineEquiv A B hAB '' S).Pairwise
        (fun p q => dist p q ∈ Set.range (Rat.cast : ℚ → ℝ)) ↔
      S.Pairwise (fun p q => dist p q ∈ Set.range (Rat.cast : ℚ → ℝ)) := by
  let e := normalizationAffineEquiv A B hAB
  constructor
  · intro h p hp q hq hpq
    apply (rational_dist_normalization_iff A B hAB hAnchor p q).mp
    exact h (Set.mem_image_of_mem e hp) (Set.mem_image_of_mem e hq)
      (fun heq => hpq (e.injective heq))
  · intro h
    rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ hpq
    apply (rational_dist_normalization_iff A B hAB hAnchor p q).mpr
    exact h hp hq (fun heq => hpq (congrArg e heq))

/-- The global similarity factor is a positive rational number: the inverse
of the positive rational anchor distance. -/
theorem exists_rational_distance_factor (A B : Plane) (hAB : A ≠ B)
    (hAnchor : dist A B ∈ Set.range (Rat.cast : ℚ → ℝ)) :
    ∃ c : ℚ, 0 < c ∧ ∀ p q : Plane,
      dist (normalizationAffineEquiv A B hAB p) (normalizationAffineEquiv A B hAB q) =
        (c : ℝ) * dist p q := by
  obtain ⟨d, hd⟩ := hAnchor
  have hdpos_real : 0 < (d : ℝ) := by
    rw [hd]
    exact dist_pos.mpr hAB
  have hdpos : 0 < d := by exact_mod_cast hdpos_real
  refine ⟨d⁻¹, inv_pos.mpr hdpos, ?_⟩
  intro p q
  rw [dist_normalizationAffineEquiv, Rat.cast_inv, hd, div_eq_mul_inv, mul_comm]

/- ## Choosing anchors and transporting the configuration -/

/-- Every given finite rational-distance configuration with at least two
points admits a normalized affine similarity. Both general-position conditions
are transported as equivalences; no general-position assumption is required. -/
theorem exists_affine_similarity_normalization {S : Set Plane} (hS : S.Finite)
    (hRat : S.Pairwise fun p q => dist p q ∈ Set.range (Rat.cast : ℚ → ℝ))
    (hcard : 2 ≤ S.ncard) :
    ∃ (e : Plane ≃ᵃ[ℝ] Plane) (c : ℚ), 0 < c ∧
      (∀ p q : Plane, dist (e p) (e q) = (c : ℝ) * dist p q) ∧
      (e '' S).Finite ∧ (e '' S).ncard = S.ncard ∧
      (NonTrilinear (e '' S) ↔ NonTrilinear S) ∧
      ((∀ Q ⊆ e '' S, Q.ncard = 4 → ¬ Cospherical Q) ↔
        (∀ Q ⊆ S, Q.ncard = 4 → ¬ Cospherical Q)) ∧
      (0 : Plane) ∈ e '' S ∧ QuadraticNormalForm.unitPoint ∈ e '' S ∧
      (e '' S).Pairwise (fun p q => dist p q ∈ Set.range (Rat.cast : ℚ → ℝ)) := by
  obtain ⟨A, B, hA, hB, hAB⟩ := (Set.one_lt_ncard_iff hS).mp (by omega)
  have hAnchor := hRat hA hB hAB
  obtain ⟨c, hc, hdist⟩ := exists_rational_distance_factor A B hAB hAnchor
  refine ⟨normalizationAffineEquiv A B hAB, c, hc, hdist, hS.image _,
    ncard_normalization A B hAB S, nonTrilinear_normalization_iff A B hAB S,
    no_four_cospherical_normalization_iff A B hAB S, ?_, ?_,
    (rational_distances_normalization_iff A B hAB hAnchor S).mpr hRat⟩
  · exact ⟨A, hA, normalizationAffineEquiv_left A B hAB⟩
  · exact ⟨B, hB, normalizationAffineEquiv_right A B hAB⟩

/-- Primary structural theorem. A given finite rational-distance configuration
with at least three points, no three collinear, and no four cospherical can be
transported by a bijective similarity of the entire plane to a configuration
containing the normalized anchors. The image has the same cardinality and
admissibility properties, still has rational distances, and has coordinates
`(x, y * sqrt d)` for one common positive rational `d`.

The similarity factor `c` and the coordinate radicand `d` are separate positive
rationals. No assertion is made about the existence of the input configuration. -/
theorem exists_similarity_quadratic_normal_form {S : Set Plane} (hS : S.Finite)
    (hRat : S.Pairwise fun p q => dist p q ∈ Set.range (Rat.cast : ℚ → ℝ))
    (htri : NonTrilinear S)
    (hfour : ∀ Q : Set Plane, Q ⊆ S ∧ Q.ncard = 4 → ¬ Cospherical Q)
    (hcard : 3 ≤ S.ncard) :
    ∃ (f : Plane ≃ Plane) (c d : ℚ), 0 < c ∧ 0 < d ∧
      (∀ p q : Plane, dist (f p) (f q) = (c : ℝ) * dist p q) ∧
      (f '' S).Finite ∧ (f '' S).ncard = S.ncard ∧
      NonTrilinear (f '' S) ∧
      (∀ Q : Set Plane, Q ⊆ f '' S ∧ Q.ncard = 4 → ¬ Cospherical Q) ∧
      (0 : Plane) ∈ f '' S ∧ QuadraticNormalForm.unitPoint ∈ f '' S ∧
      (f '' S).Pairwise (fun p q => dist p q ∈ Set.range (Rat.cast : ℚ → ℝ)) ∧
      ∀ p ∈ f '' S, ∃ x y : ℚ,
        p = !₂[(x : ℝ), (y : ℝ) * Real.sqrt (d : ℝ)] := by
  obtain ⟨e, c, hc, hdist, hfin, hncard, htri_iff, hfour_iff, h0, he, hRat_image⟩ :=
    exists_affine_similarity_normalization hS hRat (by omega)
  have htri_image := htri_iff.mpr htri
  have hfour_image := hfour_iff.mpr (fun Q hQS hQcard => hfour Q ⟨hQS, hQcard⟩)
  have hcard_image : 3 ≤ (e '' S).ncard := by rwa [hncard]
  obtain ⟨d, hd, hcoords⟩ :=
    QuadraticNormalForm.normalized_common_quadratic_field_of_nonTrilinear
      h0 he hRat_image htri_image hcard_image
  exact ⟨e.toEquiv, c, d, hc, hd, hdist, hfin, hncard, htri_image,
    (fun Q hQ => hfour_image Q hQ.1 hQ.2), h0, he, hRat_image, hcoords⟩

/-- The primary result with mathlib's imported `InGeneralPosition` predicate. -/
theorem exists_similarity_quadratic_normal_form_of_inGeneralPosition
    {S : Set Plane} (hS : S.Finite)
    (hRat : S.Pairwise fun p q => dist p q ∈ Set.range (Rat.cast : ℚ → ℝ))
    (hpos : InGeneralPosition S) (hcard : 3 ≤ S.ncard) :
    ∃ (f : Plane ≃ Plane) (c d : ℚ), 0 < c ∧ 0 < d ∧
      (∀ p q : Plane, dist (f p) (f q) = (c : ℝ) * dist p q) ∧
      (f '' S).Finite ∧ (f '' S).ncard = S.ncard ∧ InGeneralPosition (f '' S) ∧
      (0 : Plane) ∈ f '' S ∧ QuadraticNormalForm.unitPoint ∈ f '' S ∧
      (f '' S).Pairwise (fun p q => dist p q ∈ Set.range (Rat.cast : ℚ → ℝ)) ∧
      ∀ p ∈ f '' S, ∃ x y : ℚ,
        p = !₂[(x : ℝ), (y : ℝ) * Real.sqrt (d : ℝ)] := by
  obtain ⟨f, c, d, hc, hd, hdist, hfin, hncard, htri, hfour, h0, he, hRat_image,
    hcoords⟩ := exists_similarity_quadratic_normal_form hS hRat hpos.1
      (fun Q hQ => hpos.2 Q hQ.1 hQ.2) hcard
  exact ⟨f, c, d, hc, hd, hdist, hfin, hncard,
    ⟨htri, fun Q hQS hQcard => hfour Q ⟨hQS, hQcard⟩⟩, h0, he, hRat_image, hcoords⟩

/- ## Kernel dependency audit for the main constructions and results -/

#print axioms anchorReflection_sub
#print axioms anchorIsometry
#print axioms normalizationAffineEquiv
#print axioms normalizationAffineEquiv_bijective
#print axioms normalizationAffineEquiv_left
#print axioms normalizationAffineEquiv_right
#print axioms dist_normalizationAffineEquiv
#print axioms finite_normalization_iff
#print axioms ncard_normalization
#print axioms collinear_normalization_iff
#print axioms cospherical_normalization_iff
#print axioms nonTrilinear_normalization_iff
#print axioms no_four_cospherical_normalization_iff
#print axioms inGeneralPosition_normalization_iff
#print axioms rational_dist_normalization_iff
#print axioms rational_distances_normalization_iff
#print axioms exists_rational_distance_factor
#print axioms exists_affine_similarity_normalization
#print axioms exists_similarity_quadratic_normal_form
#print axioms exists_similarity_quadratic_normal_form_of_inGeneralPosition

end SimilarityNormalization
