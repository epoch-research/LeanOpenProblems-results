import FormalConjecturesUtil

/-!
# Finite integral-distance configurations in general position

This file is independent of `Submission.Spec` and `Submission.DistanceScaling`.
It verifies an explicit seven-point lattice configuration, attributed to
Kurz–Noll–Rathbun–Simmons, with diameter 2,262,000. All distances and all
noncollinearity/noncosphericity tests are certified by exact integer arithmetic.

The existence results below concern only cardinalities at most seven; they do
not assert the existence of arbitrarily large configurations.
-/

open EuclideanGeometry

namespace FiniteExamples

/-- The ordinary Euclidean plane, with its Euclidean (not sup) metric. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/- ## Coordinate criteria -/

/-- The two ordinary coordinates of a Euclidean point. -/
def coordinatePair (p : Plane) : ℝ × ℝ := (p 0, p 1)

/-- Squared Euclidean norm, as a polynomial over any commutative ring. -/
def squaredNorm {R : Type*} [CommRing R] (p : R × R) : R := p.1 ^ 2 + p.2 ^ 2

/-- The determinant of the two displacement vectors of three points. -/
def orientation {R : Type*} [CommRing R] (p q r : R × R) : R :=
  (q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1)

/-- The reduced circle determinant: the three rows are the differences from
`p` of the columns `(squared norm, x, y)`. -/
def circlePolynomial {R : Type*} [CommRing R] (p q r s : R × R) : R :=
  (squaredNorm q - squaredNorm p) *
    ((r.1 - p.1) * (s.2 - p.2) - (r.2 - p.2) * (s.1 - p.1))
  - (q.1 - p.1) *
    ((squaredNorm r - squaredNorm p) * (s.2 - p.2) -
      (r.2 - p.2) * (squaredNorm s - squaredNorm p))
  + (q.2 - p.2) *
    ((squaredNorm r - squaredNorm p) * (s.1 - p.1) -
      (r.1 - p.1) * (squaredNorm s - squaredNorm p))

/-- The standard circle matrix, with rows `(x² + y², x, y, 1)`. -/
def circleMatrix {R : Type*} [CommRing R] (p q r s : R × R) :
    Matrix (Fin 4) (Fin 4) R :=
  !![squaredNorm p, p.1, p.2, 1;
     squaredNorm q, q.1, q.2, 1;
     squaredNorm r, r.1, r.2, 1;
     squaredNorm s, s.1, s.2, 1]

/-- The reduced polynomial is the negative of the four-by-four determinant. -/
theorem circleMatrix_det {R : Type*} [CommRing R] (p q r s : R × R) :
    (circleMatrix p q r s).det = -circlePolynomial p q r s := by
  rw [Matrix.det_succ_row_zero]
  simp [circleMatrix, Matrix.det_fin_three, Matrix.submatrix_apply, Fin.sum_univ_four,
    Fin.succAbove, circlePolynomial]
  ring

/-- Squared Euclidean distance in ordinary coordinates. -/
theorem dist_sq_coordinates (p q : Plane) :
    dist p q ^ 2 = (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two]
  simp only [Real.dist_eq, sq_abs]

/-- Collinearity forces the two-by-two displacement determinant to vanish. -/
theorem collinear_orientation_eq_zero {p q r : Plane}
    (h : Collinear ℝ ({p, q, r} : Set Plane)) :
    orientation (coordinatePair p) (coordinatePair q) (coordinatePair r) = 0 := by
  obtain ⟨v, hv⟩ :=
    (collinear_iff_of_mem (show p ∈ ({p, q, r} : Set Plane) by simp)).mp h
  obtain ⟨a, ha⟩ := hv q (by simp)
  obtain ⟨b, hb⟩ := hv r (by simp)
  have ha0 := congrArg (fun z : Plane => z 0) ha
  have ha1 := congrArg (fun z : Plane => z 1) ha
  have hb0 := congrArg (fun z : Plane => z 0) hb
  have hb1 := congrArg (fun z : Plane => z 1) hb
  change q 0 = a * v 0 + p 0 at ha0
  change q 1 = a * v 1 + p 1 at ha1
  change r 0 = b * v 0 + p 0 at hb0
  change r 1 = b * v 1 + p 1 at hb1
  dsimp [orientation, coordinatePair]
  rw [ha0, ha1, hb0, hb1]
  ring

/-- Four cospherical points have singular circle matrix. The squared circle
 equations supply a nonzero vector in its kernel (its first entry is `1`). -/
theorem cospherical_circleMatrix_det_eq_zero {p q r s : Plane}
    (h : Cospherical ({p, q, r, s} : Set Plane)) :
    (circleMatrix (coordinatePair p) (coordinatePair q)
      (coordinatePair r) (coordinatePair s)).det = 0 := by
  obtain ⟨o, radius, hr⟩ := h
  let v : Fin 4 → ℝ := ![1, -2 * o 0, -2 * o 1,
    squaredNorm (coordinatePair o) - radius ^ 2]
  have heq : ∀ a ∈ ({p, q, r, s} : Set Plane),
      squaredNorm (coordinatePair a) + a 0 * (-2 * o 0) + a 1 * (-2 * o 1) +
        (squaredNorm (coordinatePair o) - radius ^ 2) = 0 := by
    intro a ha
    have hd := congrArg (fun t : ℝ => t ^ 2) (hr a ha)
    change dist a o ^ 2 = radius ^ 2 at hd
    rw [dist_sq_coordinates] at hd
    dsimp [squaredNorm, coordinatePair]
    nlinarith [hd]
  apply Matrix.exists_mulVec_eq_zero_iff.mp
  refine ⟨v, ?_, ?_⟩
  · intro hv
    have hv0 := congrArg (fun w : Fin 4 → ℝ => w 0) hv
    norm_num [v] at hv0
  · funext i
    fin_cases i
    · simpa [circleMatrix, coordinatePair, v, Matrix.mulVec, dotProduct,
        Fin.sum_univ_four] using heq p (by simp)
    · simpa [circleMatrix, coordinatePair, v, Matrix.mulVec, dotProduct,
        Fin.sum_univ_four] using heq q (by simp)
    · simpa [circleMatrix, coordinatePair, v, Matrix.mulVec, dotProduct,
        Fin.sum_univ_four] using heq r (by simp)
    · simpa [circleMatrix, coordinatePair, v, Matrix.mulVec, dotProduct,
        Fin.sum_univ_four] using heq s (by simp)

/-- Embed an integer coordinate pair in the Euclidean plane. -/
def intPoint (p : ℤ × ℤ) : Plane := !₂[(p.1 : ℝ), (p.2 : ℝ)]

/-- The coordinate embedding loses no points. -/
theorem intPoint_injective : Function.Injective intPoint := by
  intro p q hpq
  apply Prod.ext
  · apply Int.cast_injective (α := ℝ)
    exact congrArg (fun z : Plane => z 0) hpq
  · apply Int.cast_injective (α := ℝ)
    exact congrArg (fun z : Plane => z 1) hpq

/-- The displacement determinant commutes with casting integer coordinates. -/
theorem orientation_intCast (p q r : ℤ × ℤ) :
    orientation (coordinatePair (intPoint p)) (coordinatePair (intPoint q))
      (coordinatePair (intPoint r)) = (orientation p q r : ℤ) := by
  simp [orientation, coordinatePair, intPoint]

/-- The reduced circle determinant commutes with casting integer coordinates. -/
theorem circlePolynomial_intCast (p q r s : ℤ × ℤ) :
    circlePolynomial (coordinatePair (intPoint p)) (coordinatePair (intPoint q))
      (coordinatePair (intPoint r)) (coordinatePair (intPoint s)) =
        (circlePolynomial p q r s : ℤ) := by
  simp [circlePolynomial, squaredNorm, coordinatePair, intPoint]

/-- A nonzero integer displacement determinant excludes collinearity. -/
theorem not_collinear_intPoint {p q r : ℤ × ℤ} (h : orientation p q r ≠ 0) :
    ¬ Collinear ℝ ({intPoint p, intPoint q, intPoint r} : Set Plane) := by
  intro hc
  have hz := collinear_orientation_eq_zero hc
  rw [orientation_intCast] at hz
  exact h (Int.cast_eq_zero.mp hz)

/-- A nonzero integer circle determinant excludes cosphericity. -/
theorem not_cospherical_intPoint {p q r s : ℤ × ℤ}
    (h : circlePolynomial p q r s ≠ 0) :
    ¬ Cospherical ({intPoint p, intPoint q, intPoint r, intPoint s} : Set Plane) := by
  intro hc
  have hz := cospherical_circleMatrix_det_eq_zero hc
  rw [circleMatrix_det, neg_eq_zero, circlePolynomial_intCast] at hz
  exact h (Int.cast_eq_zero.mp hz)

/- ## Exact data and arithmetic certificates -/

/-- The seven lattice coordinate pairs. -/
def heptagonCoordinates : Fin 7 → ℤ × ℤ :=
  ![(0, 0), (374400, -2230800), (1081600, -1488240), (-453024, -1630200),
    (426725, -1630200), (569088, -1291680), (-439040, -1308720)]

/-- The proposed integer distance table, including the diagonal. -/
def distanceTable : Fin 7 → Fin 7 → ℤ :=
  !![0, 2262000, 1839760, 1691976, 1685125, 1411488, 1380400;
     2262000, 0, 1025440, 1022424, 602875, 959088, 1229600;
     1839760, 1025440, 0, 1541176, 670085, 548912, 1531200;
     1691976, 1022424, 1541176, 0, 879749, 1076712, 321784;
     1685125, 602875, 670085, 879749, 0, 367237, 923525;
     1411488, 959088, 548912, 1076712, 367237, 0, 1008272;
     1380400, 1229600, 1531200, 321784, 923525, 1008272, 0]

-- These are ordinary `decide` proofs, checked by Lean's kernel, not `native_decide`.
set_option maxRecDepth 10000 in
/-- The seven coordinate pairs are distinct. -/
theorem heptagonCoordinates_injective : Function.Injective heptagonCoordinates := by
  decide

set_option maxRecDepth 10000 in
/-- All triple determinants are nonzero, in every ordering of distinct indices. -/
theorem heptagon_orientation_nonzero : ∀ i j k : Fin 7,
    i ≠ j → i ≠ k → j ≠ k →
      orientation (heptagonCoordinates i) (heptagonCoordinates j)
        (heptagonCoordinates k) ≠ 0 := by
  decide

set_option maxRecDepth 10000 in
/-- All quadruple circle determinants are nonzero, in every ordering. -/
theorem heptagon_circlePolynomial_nonzero : ∀ i j k l : Fin 7,
    i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
      circlePolynomial (heptagonCoordinates i) (heptagonCoordinates j)
        (heptagonCoordinates k) (heptagonCoordinates l) ≠ 0 := by
  decide

/-- All entries of the distance table are nonnegative. -/
theorem distanceTable_nonneg : ∀ i j : Fin 7, 0 ≤ distanceTable i j := by
  decide

set_option maxRecDepth 10000 in
/-- Every squared coordinate distance equals the square of the table entry. -/
theorem heptagon_squared_distance : ∀ i j : Fin 7,
    ((heptagonCoordinates i).1 - (heptagonCoordinates j).1) ^ 2 +
      ((heptagonCoordinates i).2 - (heptagonCoordinates j).2) ^ 2 =
        distanceTable i j ^ 2 := by
  decide

/- ## The Euclidean seven-point set -/

/-- The Euclidean point with the indicated lattice coordinates. -/
def heptagonPoint (i : Fin 7) : Plane := intPoint (heptagonCoordinates i)

/-- The explicit seven-point example. -/
def heptagon : Set Plane := Set.range heptagonPoint

/-- The indexed Euclidean points are distinct. -/
theorem heptagonPoint_injective : Function.Injective heptagonPoint := by
  intro i j h
  exact heptagonCoordinates_injective (intPoint_injective h)

/-- The example is a finite set. -/
theorem finite_heptagon : heptagon.Finite := Set.finite_range _

/-- The example has exactly seven points. -/
theorem ncard_heptagon : heptagon.ncard = 7 := by
  rw [heptagon, Set.ncard_range_of_injective heptagonPoint_injective]
  simp

/-- The supplied table is the actual Euclidean distance table. -/
theorem dist_heptagonPoint (i j : Fin 7) :
    dist (heptagonPoint i) (heptagonPoint j) = (distanceTable i j : ℝ) := by
  apply (sq_eq_sq₀ dist_nonneg (show 0 ≤ (distanceTable i j : ℝ) by
    exact_mod_cast distanceTable_nonneg i j)).mp
  rw [dist_sq_coordinates]
  change (((heptagonCoordinates i).1 : ℝ) - ((heptagonCoordinates j).1 : ℝ)) ^ 2 +
    (((heptagonCoordinates i).2 : ℝ) - ((heptagonCoordinates j).2 : ℝ)) ^ 2 =
      (distanceTable i j : ℝ) ^ 2
  exact_mod_cast heptagon_squared_distance i j

/-- No three distinct points of the example are collinear, using the imported
`NonTrilinear` predicate. -/
theorem nonTrilinear_heptagon : NonTrilinear heptagon := by
  rintro p ⟨i, rfl⟩ q ⟨j, rfl⟩ r ⟨k, rfl⟩ hpq hqr hpr
  apply not_collinear_intPoint
  exact heptagon_orientation_nonzero i j k
    (fun hij => hpq (congrArg heptagonPoint hij))
    (fun hik => hpr (congrArg heptagonPoint hik))
    (fun hjk => hqr (congrArg heptagonPoint hjk))

/-- No four-element subset of the example is cospherical. -/
theorem no_four_cospherical_heptagon (Q : Set Plane)
    (hQ : Q ⊆ heptagon ∧ Q.ncard = 4) : ¬ Cospherical Q := by
  obtain ⟨p, q, r, s, hpq, hpr, hps, hqr, hqs, hrs, rfl⟩ :=
    Set.ncard_eq_four.mp hQ.2
  have hp := hQ.1 (show p ∈ ({p, q, r, s} : Set Plane) by simp)
  have hq := hQ.1 (show q ∈ ({p, q, r, s} : Set Plane) by simp)
  have hr := hQ.1 (show r ∈ ({p, q, r, s} : Set Plane) by simp)
  have hs := hQ.1 (show s ∈ ({p, q, r, s} : Set Plane) by simp)
  obtain ⟨i, rfl⟩ := hp
  obtain ⟨j, rfl⟩ := hq
  obtain ⟨k, rfl⟩ := hr
  obtain ⟨l, rfl⟩ := hs
  apply not_cospherical_intPoint
  exact heptagon_circlePolynomial_nonzero i j k l
    (fun hij => hpq (congrArg heptagonPoint hij))
    (fun hik => hpr (congrArg heptagonPoint hik))
    (fun hil => hps (congrArg heptagonPoint hil))
    (fun hjk => hqr (congrArg heptagonPoint hjk))
    (fun hjl => hqs (congrArg heptagonPoint hjl))
    (fun hkl => hrs (congrArg heptagonPoint hkl))

/-- All pairwise distances in the example belong to the integer-cast range. -/
theorem integral_distances_heptagon :
    heptagon.Pairwise fun p q => dist p q ∈ Set.range (Int.cast : ℤ → ℝ) := by
  rintro p ⟨i, rfl⟩ q ⟨j, rfl⟩ _
  exact ⟨distanceTable i j, (dist_heptagonPoint i j).symm⟩

/- ## The independent existence predicate and subset cases -/

/-- There exists a finite `n`-point Euclidean configuration with no three
collinear points, no four cospherical points, and integral pairwise distances.
This is defined independently of the specification module. -/
def IntegralConfiguration (n : ℕ) : Prop :=
  ∃ S : Set Plane, S.Finite ∧ S.ncard = n ∧ NonTrilinear S ∧
    (∀ Q : Set Plane, Q ⊆ S ∧ Q.ncard = 4 → ¬ Cospherical Q) ∧
    (S.Pairwise fun p q => dist p q ∈ Set.range (Int.cast : ℤ → ℝ))

/-- A genuine seven-point integral-distance configuration in general position. -/
theorem integralConfiguration_seven : IntegralConfiguration 7 :=
  ⟨heptagon, finite_heptagon, ncard_heptagon, nonTrilinear_heptagon,
    no_four_cospherical_heptagon, integral_distances_heptagon⟩

/-- Taking a subset preserves every admissibility condition and permits any
smaller cardinality, including zero. -/
theorem IntegralConfiguration.mono {m n : ℕ} (hm : IntegralConfiguration m)
    (hnm : n ≤ m) : IntegralConfiguration n := by
  obtain ⟨S, hfin, hcard, hline, hcircle, hdist⟩ := hm
  have hns : n ≤ S.ncard := by simpa only [hcard] using hnm
  obtain ⟨T, hTS, hTcard⟩ := Set.exists_subset_card_eq hns
  refine ⟨T, hfin.subset hTS, hTcard, Set.Triplewise.mono hTS hline, ?_,
    Set.Pairwise.mono hTS hdist⟩
  intro Q hQ
  exact hcircle Q ⟨hQ.1.trans hTS, hQ.2⟩

/-- All cardinalities at most seven admit such a configuration.
No assertion is made here for `n > 7`. -/
theorem integralConfiguration_of_le_seven (n : ℕ) (hn : n ≤ 7) :
    IntegralConfiguration n :=
  integralConfiguration_seven.mono hn

/- ## Axiom audit -/

#print axioms heptagon_orientation_nonzero
#print axioms heptagon_circlePolynomial_nonzero
#print axioms integralConfiguration_seven
#print axioms IntegralConfiguration.mono
#print axioms integralConfiguration_of_le_seven

end FiniteExamples
