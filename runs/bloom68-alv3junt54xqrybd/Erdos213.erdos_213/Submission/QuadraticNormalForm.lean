import FormalConjecturesUtil
import Submission.FiniteExamples

/-!
# A common quadratic coordinate field for normalized rational-distance sets

For a subset of the Euclidean plane containing `0` and `(1, 0)`, rational
pairwise distances force every first coordinate to be rational. If one point
has a nonzero second coordinate, all second coordinates are rational multiples
of that same coordinate, whose square is a positive rational number. Thus the
whole set has coordinates `(x, y * sqrt d)` for a single positive `d : ℚ`.

The set need not be finite. These are necessary coordinate restrictions, not
an existence theorem for arbitrary-size distance configurations. This file is
independent of the specification module.
-/

open EuclideanGeometry

namespace QuadraticNormalForm

/-- The Euclidean plane, equipped with its Euclidean metric. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The second anchor in a normalized configuration. -/
def unitPoint : Plane := !₂[1, 0]

/- ## Rational coordinate identities -/

/-- A pairwise rational-distance hypothesis also gives rational distances on
all diagonal pairs. No finiteness assumption is needed. -/
theorem rational_distances_all {α : Type*} [PseudoMetricSpace α] {S : Set α}
    (hRat : S.Pairwise fun p q => dist p q ∈ Set.range (Rat.cast : ℚ → ℝ))
    {p q : α} (hp : p ∈ S) (hq : q ∈ S) :
    dist p q ∈ Set.range (Rat.cast : ℚ → ℝ) := by
  classical
  by_cases hpq : p = q
  · subst q
    exact ⟨0, by simp⟩
  · exact hRat hp hq hpq

/-- Distances to the normalized anchors determine a rational first coordinate:
`p₀ = (dist(p,0)² - dist(p,(1,0))² + 1) / 2`. -/
theorem first_coordinate_rational {S : Set Plane}
    (h0 : (0 : Plane) ∈ S) (he : unitPoint ∈ S)
    (hRat : S.Pairwise fun p q => dist p q ∈ Set.range (Rat.cast : ℚ → ℝ))
    {p : Plane} (hp : p ∈ S) :
    p 0 ∈ Set.range (Rat.cast : ℚ → ℝ) := by
  obtain ⟨r0, hr0⟩ := rational_distances_all hRat hp h0
  obtain ⟨r1, hr1⟩ := rational_distances_all hRat hp he
  have hd0 : (r0 : ℝ) ^ 2 = p 0 ^ 2 + p 1 ^ 2 := by
    rw [hr0, FiniteExamples.dist_sq_coordinates]
    simp
  have hd1 : (r1 : ℝ) ^ 2 = (p 0 - 1) ^ 2 + p 1 ^ 2 := by
    rw [hr1, FiniteExamples.dist_sq_coordinates]
    simp [unitPoint]
  refine ⟨(r0 ^ 2 - r1 ^ 2 + 1) / 2, ?_⟩
  push_cast
  nlinarith [hd0, hd1]

/-- The square of every second coordinate is rational. -/
theorem second_coordinate_sq_rational {S : Set Plane}
    (h0 : (0 : Plane) ∈ S) (he : unitPoint ∈ S)
    (hRat : S.Pairwise fun p q => dist p q ∈ Set.range (Rat.cast : ℚ → ℝ))
    {p : Plane} (hp : p ∈ S) :
    p 1 ^ 2 ∈ Set.range (Rat.cast : ℚ → ℝ) := by
  obtain ⟨r, hr⟩ := rational_distances_all hRat hp h0
  obtain ⟨x, hx⟩ := first_coordinate_rational h0 he hRat hp
  have hd : (r : ℝ) ^ 2 = p 0 ^ 2 + p 1 ^ 2 := by
    rw [hr, FiniteExamples.dist_sq_coordinates]
    simp
  refine ⟨r ^ 2 - x ^ 2, ?_⟩
  push_cast
  rw [hx]
  nlinarith [hd]

/-- Polarization shows that the product of any two second coordinates is
rational, even when the two points coincide. -/
theorem vertical_product_rational {S : Set Plane}
    (h0 : (0 : Plane) ∈ S) (he : unitPoint ∈ S)
    (hRat : S.Pairwise fun p q => dist p q ∈ Set.range (Rat.cast : ℚ → ℝ))
    {p q : Plane} (hp : p ∈ S) (hq : q ∈ S) :
    p 1 * q 1 ∈ Set.range (Rat.cast : ℚ → ℝ) := by
  obtain ⟨rp, hrp⟩ := rational_distances_all hRat hp h0
  obtain ⟨rq, hrq⟩ := rational_distances_all hRat hq h0
  obtain ⟨rpq, hrpq⟩ := rational_distances_all hRat hp hq
  obtain ⟨x, hx⟩ := first_coordinate_rational h0 he hRat hp
  obtain ⟨z, hz⟩ := first_coordinate_rational h0 he hRat hq
  have hdp : (rp : ℝ) ^ 2 = p 0 ^ 2 + p 1 ^ 2 := by
    rw [hrp, FiniteExamples.dist_sq_coordinates]
    simp
  have hdq : (rq : ℝ) ^ 2 = q 0 ^ 2 + q 1 ^ 2 := by
    rw [hrq, FiniteExamples.dist_sq_coordinates]
    simp
  have hdpq : (rpq : ℝ) ^ 2 = (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 := by
    rw [hrpq, FiniteExamples.dist_sq_coordinates]
  refine ⟨(rp ^ 2 + rq ^ 2 - rpq ^ 2 - 2 * x * z) / 2, ?_⟩
  push_cast
  rw [hx, hz]
  nlinarith [hdp, hdq, hdpq]

/-- Fixing one point off the first-coordinate axis expresses every second
coordinate as a rational multiple of its second coordinate. -/
theorem vertical_coordinate_rational_multiple {S : Set Plane}
    (h0 : (0 : Plane) ∈ S) (he : unitPoint ∈ S)
    (hRat : S.Pairwise fun p q => dist p q ∈ Set.range (Rat.cast : ℚ → ℝ))
    {c : Plane} (hc : c ∈ S) (hcy : c 1 ≠ 0)
    {p : Plane} (hp : p ∈ S) :
    ∃ b : ℚ, p 1 = (b : ℝ) * c 1 := by
  obtain ⟨d, hd⟩ := second_coordinate_sq_rational h0 he hRat hc
  obtain ⟨t, ht⟩ := vertical_product_rational h0 he hRat hp hc
  refine ⟨t / d, ?_⟩
  push_cast
  rw [hd, ht]
  field_simp [hcy]

/- ## The common quadratic coordinate field -/

/-- The intermediate common-generator form. The generator can be chosen as
the second coordinate of any point off the first-coordinate axis. -/
theorem normalized_common_vertical_generator {S : Set Plane}
    (h0 : (0 : Plane) ∈ S) (he : unitPoint ∈ S)
    (hRat : S.Pairwise fun p q => dist p q ∈ Set.range (Rat.cast : ℚ → ℝ))
    (hoff : ∃ c ∈ S, c 1 ≠ 0) :
    ∃ h : ℝ, h ≠ 0 ∧ h ^ 2 ∈ Set.range (Rat.cast : ℚ → ℝ) ∧
      ∀ p ∈ S, p 0 ∈ Set.range (Rat.cast : ℚ → ℝ) ∧
        ∃ b : ℚ, p 1 = (b : ℝ) * h := by
  obtain ⟨c, hc, hcy⟩ := hoff
  refine ⟨c 1, hcy, second_coordinate_sq_rational h0 he hRat hc, ?_⟩
  intro p hp
  exact ⟨first_coordinate_rational h0 he hRat hp,
    vertical_coordinate_rational_multiple h0 he hRat hc hcy hp⟩

/-- A nonzero common generator with rational square can be replaced by the
positive square root of that rational square. Negative generators only change
the signs of the rational second-coordinate coefficients. -/
theorem quadratic_normal_form_of_common_generator {S : Set Plane} {h : ℝ}
    (hne : h ≠ 0) (hsq : h ^ 2 ∈ Set.range (Rat.cast : ℚ → ℝ))
    (hcoords : ∀ p ∈ S, p 0 ∈ Set.range (Rat.cast : ℚ → ℝ) ∧
      ∃ b : ℚ, p 1 = (b : ℝ) * h) :
    ∃ d : ℚ, 0 < d ∧ ∀ p ∈ S, ∃ x y : ℚ,
      p = !₂[(x : ℝ), (y : ℝ) * Real.sqrt (d : ℝ)] := by
  obtain ⟨d, hd⟩ := hsq
  have hdpos_real : 0 < (d : ℝ) := by
    rw [hd]
    exact sq_pos_of_ne_zero hne
  have hdpos : 0 < d := by exact_mod_cast hdpos_real
  have hsqrt : Real.sqrt (d : ℝ) = |h| := by
    rw [hd, Real.sqrt_sq_eq_abs]
  refine ⟨d, hdpos, ?_⟩
  intro p hp
  obtain ⟨⟨x, hx⟩, b, hb⟩ := hcoords p hp
  by_cases hsign : 0 ≤ h
  · refine ⟨x, b, ?_⟩
    ext i
    fin_cases i
    · simpa using hx.symm
    · simpa [hsqrt, abs_of_nonneg hsign] using hb
  · refine ⟨x, -b, ?_⟩
    ext i
    fin_cases i
    · simpa using hx.symm
    · simpa [hsqrt, abs_of_neg (lt_of_not_ge hsign)] using hb

/-- Every normalized rational-distance set with a point off the anchor axis
has one common positive rational quadratic radicand for all coordinates.
Neither finiteness nor a general-position assumption is required. -/
theorem normalized_common_quadratic_field {S : Set Plane}
    (h0 : (0 : Plane) ∈ S) (he : unitPoint ∈ S)
    (hRat : S.Pairwise fun p q => dist p q ∈ Set.range (Rat.cast : ℚ → ℝ))
    (hoff : ∃ c ∈ S, c 1 ≠ 0) :
    ∃ d : ℚ, 0 < d ∧ ∀ p ∈ S, ∃ x y : ℚ,
      p = !₂[(x : ℝ), (y : ℝ) * Real.sqrt (d : ℝ)] := by
  obtain ⟨h, hne, hsq, hcoords⟩ :=
    normalized_common_vertical_generator h0 he hRat hoff
  exact quadratic_normal_form_of_common_generator hne hsq hcoords

/- ## The nontrilinear hypothesis supplies an off-axis point -/

/-- A normalized nontrilinear set with at least three points cannot be
contained in the first-coordinate axis. -/
theorem exists_off_axis_of_nonTrilinear {S : Set Plane}
    (h0 : (0 : Plane) ∈ S) (htri : NonTrilinear S) (hcard : 3 ≤ S.ncard) :
    ∃ c ∈ S, c 1 ≠ 0 := by
  classical
  by_contra hoff
  push_neg at hoff
  have hcol : Collinear ℝ S := by
    apply (collinear_iff_of_mem h0).mpr
    refine ⟨unitPoint, ?_⟩
    intro p hp
    refine ⟨p 0, ?_⟩
    ext i
    fin_cases i
    · simp [unitPoint]
    · simpa [unitPoint] using hoff p hp
  have hfin : S.Finite := Set.finite_of_ncard_pos (by omega)
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ :=
    (Set.two_lt_ncard_iff hfin).mp (by omega)
  apply htri ha hb hc hab hbc hac
  exact Collinear.subset (by simp [Set.insert_subset_iff, ha, hb, hc]) hcol

/-- The common-generator version under the usual nontrilinear and
at-least-three-points assumptions. -/
theorem normalized_common_vertical_generator_of_nonTrilinear {S : Set Plane}
    (h0 : (0 : Plane) ∈ S) (he : unitPoint ∈ S)
    (hRat : S.Pairwise fun p q => dist p q ∈ Set.range (Rat.cast : ℚ → ℝ))
    (htri : NonTrilinear S) (hcard : 3 ≤ S.ncard) :
    ∃ h : ℝ, h ≠ 0 ∧ h ^ 2 ∈ Set.range (Rat.cast : ℚ → ℝ) ∧
      ∀ p ∈ S, p 0 ∈ Set.range (Rat.cast : ℚ → ℝ) ∧
        ∃ b : ℚ, p 1 = (b : ℝ) * h :=
  normalized_common_vertical_generator h0 he hRat
    (exists_off_axis_of_nonTrilinear h0 htri hcard)

/-- The normalized quadratic coordinate normal form under the usual
nontrilinear and at-least-three-points assumptions. -/
theorem normalized_common_quadratic_field_of_nonTrilinear {S : Set Plane}
    (h0 : (0 : Plane) ∈ S) (he : unitPoint ∈ S)
    (hRat : S.Pairwise fun p q => dist p q ∈ Set.range (Rat.cast : ℚ → ℝ))
    (htri : NonTrilinear S) (hcard : 3 ≤ S.ncard) :
    ∃ d : ℚ, 0 < d ∧ ∀ p ∈ S, ∃ x y : ℚ,
      p = !₂[(x : ℝ), (y : ℝ) * Real.sqrt (d : ℝ)] :=
  normalized_common_quadratic_field h0 he hRat
    (exists_off_axis_of_nonTrilinear h0 htri hcard)

/- ## Three-anchor trilateration -/

/-- Distances to three anchors with nonzero coordinate orientation uniquely
determine a point of the Euclidean plane. No distance-rationality hypothesis
is needed. -/
theorem three_anchor_trilateration {a b c p q : Plane}
    (horient : FiniteExamples.orientation (FiniteExamples.coordinatePair a)
      (FiniteExamples.coordinatePair b) (FiniteExamples.coordinatePair c) ≠ 0)
    (ha : dist p a = dist q a) (hb : dist p b = dist q b)
    (hc : dist p c = dist q c) : p = q := by
  have hda : dist p a ^ 2 = dist q a ^ 2 := congrArg (fun t : ℝ => t ^ 2) ha
  have hdb : dist p b ^ 2 = dist q b ^ 2 := congrArg (fun t : ℝ => t ^ 2) hb
  have hdc : dist p c ^ 2 = dist q c ^ 2 := congrArg (fun t : ℝ => t ^ 2) hc
  rw [FiniteExamples.dist_sq_coordinates, FiniteExamples.dist_sq_coordinates] at hda hdb hdc
  have hlinb : (p 0 - q 0) * (b 0 - a 0) + (p 1 - q 1) * (b 1 - a 1) = 0 := by
    nlinarith only [hda, hdb]
  have hlinc : (p 0 - q 0) * (c 0 - a 0) + (p 1 - q 1) * (c 1 - a 1) = 0 := by
    nlinarith only [hda, hdc]
  have hdet : (b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0) ≠ 0 :=
    horient
  have hxdet : (p 0 - q 0) *
      ((b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0)) = 0 := by
    linear_combination (c 1 - a 1) * hlinb - (b 1 - a 1) * hlinc
  have hydet : (p 1 - q 1) *
      ((b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0)) = 0 := by
    linear_combination (b 0 - a 0) * hlinc - (c 0 - a 0) * hlinb
  have hx : p 0 = q 0 := sub_eq_zero.mp ((mul_eq_zero.mp hxdet).resolve_right hdet)
  have hy : p 1 = q 1 := sub_eq_zero.mp ((mul_eq_zero.mp hydet).resolve_right hdet)
  ext i
  fin_cases i
  · exact hx
  · exact hy

/- ## Axiom audit -/

#print axioms rational_distances_all
#print axioms first_coordinate_rational
#print axioms second_coordinate_sq_rational
#print axioms vertical_product_rational
#print axioms vertical_coordinate_rational_multiple
#print axioms normalized_common_vertical_generator
#print axioms quadratic_normal_form_of_common_generator
#print axioms normalized_common_quadratic_field
#print axioms exists_off_axis_of_nonTrilinear
#print axioms normalized_common_vertical_generator_of_nonTrilinear
#print axioms normalized_common_quadratic_field_of_nonTrilinear
#print axioms three_anchor_trilateration

end QuadraticNormalForm
