import FormalConjecturesUtil

/-!
# Auxiliary seven-color upper bound
Adapted from Egor Lyfar’s Apache-2.0 Lean Pool formalization of Isbell’s coloring.
This is only an upper bound and does not settle either theorem in Spec.lean.
-/


/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/


/-
# Plane unit-distance graph and triangular lattice

This module defines the Euclidean plane graph and the lattice geometry used by
the seven-color construction.
-/

namespace HadwigerNelsonBounds

open SimpleGraph

/-- The plane R² as a 2-dimensional Euclidean space. -/
abbrev R2 : Type := EuclideanSpace ℝ (Fin 2)

/-- The unit-distance graph on R²: vertices are points of the plane, with
    an edge between `p` and `q` iff `dist p q = 1`. Built via
    `SimpleGraph.fromRel`, which automatically symmetrizes the relation
    and removes self-loops (`dist p p = 0 ≠ 1`, so this is harmless). -/
def unitDistanceGraph : SimpleGraph R2 :=
  SimpleGraph.fromRel (fun p q => dist p q = 1)

/-- Adjacency unfolds to: distinct points at distance exactly 1. -/
@[simp] lemma unitDistanceGraph_adj (p q : R2) :
    unitDistanceGraph.Adj p q ↔ p ≠ q ∧ (dist p q = 1 ∨ dist q p = 1) := by
  unfold unitDistanceGraph
  exact SimpleGraph.fromRel_adj _ _ _

/- ### Isbell hexagonal-tiling 7-coloring -/

/-- Lattice basis spacing. Any value in the interval
    `(1/(√7 − 2/√3), √3/2) ≈ (0.671, 0.866)` is geometrically valid;
    we pick the clean rational `3/4`. -/
noncomputable def isbellLatticeStep : ℝ := 3 / 4

/-- The triangular-lattice point at integer coords `(i, j)`:
    `i · (a, 0) + j · (a/2, a·√3/2)`. -/
noncomputable def isbellLatticePoint (i j : ℤ) : R2 :=
  WithLp.toLp 2
    ![(i : ℝ) * isbellLatticeStep + (j : ℝ) * (isbellLatticeStep / 2),
      (j : ℝ) * (isbellLatticeStep * Real.sqrt 3 / 2)]

@[simp] lemma isbellLatticePoint_zero (i j : ℤ) :
    (isbellLatticePoint i j) 0
      = (i : ℝ) * isbellLatticeStep + (j : ℝ) * (isbellLatticeStep / 2) := rfl

@[simp] lemma isbellLatticePoint_one (i j : ℤ) :
    (isbellLatticePoint i j) 1
      = (j : ℝ) * (isbellLatticeStep * Real.sqrt 3 / 2) := rfl

/-- `√3 * √3 = 3`, hoisted to file scope for use in the squared-distance
    computation. -/
lemma sqrt_three_mul_self : Real.sqrt 3 * Real.sqrt 3 = 3 :=
  Real.mul_self_sqrt (by norm_num)

/-- Squared Euclidean distance between two lattice points. -/
lemma isbellLatticePoint_dist_sq (i j i' j' : ℤ) :
    dist (isbellLatticePoint i j) (isbellLatticePoint i' j') ^ 2
      = isbellLatticeStep ^ 2 *
          (((i : ℝ) - i') ^ 2 + ((i : ℝ) - i') * ((j : ℝ) - j') + ((j : ℝ) - j') ^ 2) := by
  rw [PiLp.dist_sq_eq_of_L2]
  simp only [Fin.sum_univ_two, isbellLatticePoint_zero, isbellLatticePoint_one,
    Real.dist_eq, sq_abs]
  have hsq3 : Real.sqrt 3 * Real.sqrt 3 = 3 := sqrt_three_mul_self
  -- Use ring manipulations and the sqrt fact.
  have h0 : ((i : ℝ) * isbellLatticeStep + (j : ℝ) * (isbellLatticeStep / 2)
            - ((i' : ℝ) * isbellLatticeStep + (j' : ℝ) * (isbellLatticeStep / 2)))
          = isbellLatticeStep * (((i : ℝ) - i') + ((j : ℝ) - j') / 2) := by ring
  have h1 : ((j : ℝ) * (isbellLatticeStep * Real.sqrt 3 / 2)
            - (j' : ℝ) * (isbellLatticeStep * Real.sqrt 3 / 2))
          = isbellLatticeStep * Real.sqrt 3 / 2 * ((j : ℝ) - j') := by ring
  rw [h0, h1]
  have h0sq : (isbellLatticeStep * (((i : ℝ) - i') + ((j : ℝ) - j') / 2)) ^ 2
            = isbellLatticeStep ^ 2 *
                (((i : ℝ) - i') ^ 2 + ((i : ℝ) - i') * ((j : ℝ) - j')
                  + ((j : ℝ) - j') ^ 2 / 4) := by ring
  have h1sq : (isbellLatticeStep * Real.sqrt 3 / 2 * ((j : ℝ) - j')) ^ 2
            = isbellLatticeStep ^ 2 * (Real.sqrt 3 * Real.sqrt 3) / 4
                * ((j : ℝ) - j') ^ 2 := by ring
  rw [h0sq, h1sq, hsq3]
  ring

/-
**Voronoi covering radius (the geometric heart of (G1)).** For every
point `p ∈ R²`, some lattice point lies within distance `a/√3` of `p`.

Equivalently: the closed Voronoi cells (regular hexagons of
circumradius `a/√3`) around each lattice point cover the entire
plane.

We prove it constructively below by rounding lattice coordinates and
case-splitting on the four Voronoi cells that cover `[0, 1)²` in
lattice-coordinate parameter space.
-/

/-- Squared Euclidean distance from a point `p : R²` to a lattice point.
    Helper formula expressed directly in terms of `p 0`, `p 1`, `i`, `j`. -/
lemma dist_point_lattice_sq_cart (p : R2) (i j : ℤ) :
    dist p (isbellLatticePoint i j) ^ 2
      = (p 0 - ((i : ℝ) * isbellLatticeStep + (j : ℝ) * (isbellLatticeStep / 2))) ^ 2
        + (p 1 - (j : ℝ) * (isbellLatticeStep * Real.sqrt 3 / 2)) ^ 2 := by
  rw [PiLp.dist_sq_eq_of_L2]
  simp only [Fin.sum_univ_two, isbellLatticePoint_zero, isbellLatticePoint_one,
    Real.dist_eq, sq_abs]

/-- The Voronoi covering bound `Q(u, v) ≤ 1/3` holds in the centroid region
    of the triangle with vertices `(0,0), (1,0), (0,1)`. -/
lemma Q_le_third_origin {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (h1 : 2 * α + β ≤ 1) (h2 : α + 2 * β ≤ 1) :
    α ^ 2 + α * β + β ^ 2 ≤ 1 / 3 := by
  -- Max of α² + αβ + β² over {α,β ≥ 0, 2α+β ≤ 1, α+2β ≤ 1} is 1/3 at (1/3, 1/3).
  -- Use nlinarith with the constraint products.
  nlinarith [sq_nonneg α, sq_nonneg β, sq_nonneg (α + β),
    sq_nonneg (α - β), sq_nonneg (1 - 3*α - 3*β), sq_nonneg (3*α - 1),
    sq_nonneg (3*β - 1), sq_nonneg (3 * α + 3 * β - 2), hα, hβ, h1, h2,
    mul_nonneg hα hβ,
    mul_nonneg hα (sub_nonneg.mpr h1),
    mul_nonneg hβ (sub_nonneg.mpr h2)]

end HadwigerNelsonBounds

/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/


/-
# Voronoi quadratic-form bounds

This module proves that one of the four corners of a lattice-coordinate unit
square lies within the required quadratic-form radius.
-/

namespace HadwigerNelsonBounds

private lemma cornerZeroZero_le_third {α β : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hFirst : 2 * α + β ≤ 1) (hSecond : α + 2 * β ≤ 1) :
    α ^ 2 + α * β + β ^ 2 ≤ 1 / 3 :=
  Q_le_third_origin hα hβ hFirst hSecond

private lemma cornerZeroOne_lower_le_third {α β : ℝ}
    (hα : 0 ≤ α) (hDiagonal : α + β ≤ 1)
    (hFront : 1 ≤ α + 2 * β)
    (hOrder : α ≤ β) :
    α ^ 2 + α * (β - 1) + (β - 1) ^ 2 ≤ 1 / 3 := by
  have hIdentity :
      α ^ 2 + α * (β - 1) + (β - 1) ^ 2 =
        (1 - α - β) ^ 2 + (1 - α - β) * α + α ^ 2 := by
    ring
  rw [hIdentity]
  apply Q_le_third_origin
  · linarith
  · linarith
  · linarith
  · linarith

private lemma cornerOneZero_lower_le_third {α β : ℝ}
    (hβ : 0 ≤ β) (hDiagonal : α + β ≤ 1)
    (hFront : 1 ≤ 2 * α + β)
    (hOrder : β ≤ α) :
    (α - 1) ^ 2 + (α - 1) * β + β ^ 2 ≤ 1 / 3 := by
  have hIdentity :
      (α - 1) ^ 2 + (α - 1) * β + β ^ 2 =
        β ^ 2 + β * (1 - α - β) + (1 - α - β) ^ 2 := by
    ring
  rw [hIdentity]
  apply Q_le_third_origin
  · linarith
  · linarith
  · linarith
  · linarith

private lemma cornerOneOne_le_third {α β : ℝ}
    (hα : α < 1) (hβ : β < 1)
    (hFirst : 2 ≤ 2 * α + β) (hSecond : 2 ≤ α + 2 * β) :
    (α - 1) ^ 2 + (α - 1) * (β - 1) + (β - 1) ^ 2 ≤ 1 / 3 := by
  have hIdentity :
      (α - 1) ^ 2 + (α - 1) * (β - 1) + (β - 1) ^ 2 =
        (1 - α) ^ 2 + (1 - α) * (1 - β) + (1 - β) ^ 2 := by
    ring
  rw [hIdentity]
  apply Q_le_third_origin
  · linarith
  · linarith
  · linarith
  · linarith

private lemma cornerOneZero_upper_le_third {α β : ℝ}
    (hDiagonal : 1 ≤ α + β) (hα : α < 1)
    (hBack : α + 2 * β ≤ 2) (hOrder : β ≤ α) :
    (α - 1) ^ 2 + (α - 1) * β + β ^ 2 ≤ 1 / 3 := by
  have hIdentity :
      (α - 1) ^ 2 + (α - 1) * β + β ^ 2 =
        (α + β - 1) ^ 2 + (α + β - 1) * (1 - α) + (1 - α) ^ 2 := by
    ring
  rw [hIdentity]
  apply Q_le_third_origin
  · linarith
  · linarith
  · linarith
  · linarith

private lemma cornerZeroOne_upper_le_third {α β : ℝ}
    (hDiagonal : 1 ≤ α + β) (hβ : β < 1)
    (hOrder : α ≤ β) (hBack : 2 * α + β ≤ 2) :
    α ^ 2 + α * (β - 1) + (β - 1) ^ 2 ≤ 1 / 3 := by
  have hIdentity :
      α ^ 2 + α * (β - 1) + (β - 1) ^ 2 =
        (1 - β) ^ 2 + (1 - β) * (α + β - 1) + (α + β - 1) ^ 2 := by
    ring
  rw [hIdentity]
  apply Q_le_third_origin
  · linarith
  · linarith
  · linarith
  · linarith

/-- Every point of the half-open lattice-coordinate unit square lies within
quadratic-form radius 1 / 3 of one of its four corners. -/
lemma unitSquare_has_near_lattice_corner {α β : ℝ}
    (hαLower : 0 ≤ α) (hαUpper : α < 1)
    (hβLower : 0 ≤ β) (hβUpper : β < 1) :
    ∃ Δi Δj : ℤ,
      (α - (Δi : ℝ)) ^ 2 +
        (α - (Δi : ℝ)) * (β - (Δj : ℝ)) +
        (β - (Δj : ℝ)) ^ 2 ≤ 1 / 3 := by
  by_cases hFirst : 2 * α + β ≤ 1
  · by_cases hSecond : α + 2 * β ≤ 1
    · refine ⟨0, 0, ?_⟩
      simpa using
        cornerZeroZero_le_third hαLower hβLower hFirst hSecond
    · have hSecond' : 1 ≤ α + 2 * β := le_of_lt (not_le.mp hSecond)
      have hDiagonal : α + β ≤ 1 := by linarith
      have hOrder : α ≤ β := by linarith
      refine ⟨0, 1, ?_⟩
      simpa using
        cornerZeroOne_lower_le_third
          hαLower hDiagonal hSecond' hOrder
  · have hFirst' : 1 ≤ 2 * α + β := le_of_lt (not_le.mp hFirst)
    by_cases hTop : 2 ≤ 2 * α + β
    · by_cases hTopSecond : 2 ≤ α + 2 * β
      · refine ⟨1, 1, ?_⟩
        simpa using
          cornerOneOne_le_third hαUpper hβUpper hTop hTopSecond
      · have hTopSecond' : α + 2 * β ≤ 2 :=
          le_of_lt (not_le.mp hTopSecond)
        have hDiagonal : 1 ≤ α + β := by linarith
        have hOrder : β ≤ α := by linarith
        refine ⟨1, 0, ?_⟩
        simpa using
          cornerOneZero_upper_le_third
            hDiagonal hαUpper hTopSecond' hOrder
    · have hTop' : 2 * α + β ≤ 2 := le_of_lt (not_le.mp hTop)
      by_cases hDiagonal : α + β ≤ 1
      · by_cases hSecond : α + 2 * β ≤ 1
        · have hOrder : β ≤ α := by linarith
          refine ⟨1, 0, ?_⟩
          simpa using
            cornerOneZero_lower_le_third
              hβLower hDiagonal hFirst' hOrder
        · have hSecond' : 1 ≤ α + 2 * β :=
            le_of_lt (not_le.mp hSecond)
          by_cases hOrder : β ≤ α
          · refine ⟨1, 0, ?_⟩
            simpa using
              cornerOneZero_lower_le_third
                hβLower hDiagonal hFirst' hOrder
          · have hOrder' : α ≤ β := le_of_lt (not_le.mp hOrder)
            refine ⟨0, 1, ?_⟩
            simpa using
              cornerZeroOne_lower_le_third
                hαLower hDiagonal hSecond' hOrder'
      · have hDiagonal' : 1 ≤ α + β :=
          le_of_lt (not_le.mp hDiagonal)
        by_cases hOrder : β ≤ α
        · have hBack : α + 2 * β ≤ 2 := by linarith
          refine ⟨1, 0, ?_⟩
          simpa using
            cornerOneZero_upper_le_third
              hDiagonal' hαUpper hBack hOrder
        · have hOrder' : α ≤ β := le_of_lt (not_le.mp hOrder)
          refine ⟨0, 1, ?_⟩
          simpa using
            cornerZeroOne_upper_le_third
              hDiagonal' hβUpper hOrder' hTop'

end HadwigerNelsonBounds

/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/


/-
# Triangular-lattice covering radius

This module converts the unit-square quadratic estimate into a covering-radius
theorem for the triangular lattice and defines the chosen nearest lattice cell.
-/

namespace HadwigerNelsonBounds

open SimpleGraph

/-- **Voronoi covering radius (the geometric heart of (G1)).**

    Constructive proof: given `p ∈ R²`, compute lattice coordinates
    `s := p₀/a − p₁/(a√3)`, `t := 2·p₁/(a√3)`. Let
    `i₀ := ⌊s⌋`, `j₀ := ⌊t⌋`,
    `α := s − i₀ ∈ [0, 1)`, `β := t − j₀ ∈ [0, 1)`. The squared distance from
    `p` to lattice point `(i₀ + Δi, j₀ + Δj)` is `a²·Q(α − Δi, β − Δj)` where
    `Q(u, v) = u² + uv + v²`.

    The unit square `[0, 1]²` is covered by four Voronoi cells centered at
    `(0,0), (1,0), (0,1), (1,1)` in `(α, β)` space. In each cell, the
    corresponding `Q` value is `≤ 1/3`. Case-split on the cell. -/
lemma exists_lattice_point_within_circumradius (p : R2) :
    ∃ (q : ℤ × ℤ), dist p (isbellLatticePoint q.1 q.2)
                    ≤ isbellLatticeStep / Real.sqrt 3 := by
  -- Abbreviations.
  set a := isbellLatticeStep with ha_def
  have ha_pos : 0 < a := by
    change (0 : ℝ) < isbellLatticeStep
    unfold isbellLatticeStep
    norm_num
  have ha_ne : a ≠ 0 := ne_of_gt ha_pos
  have hsqrt3_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hsqrt3_ne : Real.sqrt 3 ≠ 0 := ne_of_gt hsqrt3_pos
  have hsq3 : Real.sqrt 3 * Real.sqrt 3 = 3 := sqrt_three_mul_self
  -- Lattice coordinates of p.
  set s : ℝ := p 0 / a - p 1 / (a * Real.sqrt 3) with hs_def
  set t : ℝ := 2 * p 1 / (a * Real.sqrt 3) with ht_def
  -- Inverse: p 0 = s·a + t·a/2 and p 1 = t·a·√3/2.
  have hp0_eq : p 0 = s * a + t * (a / 2) := by
    change p 0 = (p 0 / a - p 1 / (a * Real.sqrt 3)) * a
      + (2 * p 1 / (a * Real.sqrt 3)) * (a / 2)
    field_simp
    ring
  have hp1_eq : p 1 = t * (a * Real.sqrt 3 / 2) := by
    change p 1 = (2 * p 1 / (a * Real.sqrt 3)) * (a * Real.sqrt 3 / 2)
    field_simp
  -- Floor + fractional part.
  set i₀ : ℤ := ⌊s⌋ with hi₀_def
  set j₀ : ℤ := ⌊t⌋ with hj₀_def
  set α : ℝ := s - (i₀ : ℝ) with hα_def
  set β : ℝ := t - (j₀ : ℝ) with hβ_def
  -- α, β ∈ [0, 1).
  have hα_lo : 0 ≤ α := by
    change 0 ≤ s - (i₀ : ℝ)
    have := Int.floor_le s
    linarith
  have hα_hi : α < 1 := by
    change s - (i₀ : ℝ) < 1
    have := Int.lt_floor_add_one s
    linarith
  have hβ_lo : 0 ≤ β := by
    change 0 ≤ t - (j₀ : ℝ)
    have := Int.floor_le t
    linarith
  have hβ_hi : β < 1 := by
    change t - (j₀ : ℝ) < 1
    have := Int.lt_floor_add_one t
    linarith
  -- Distance-squared formula (parametrized in Δi, Δj relative to (i₀, j₀)).
  -- Squared dist from p to lattice(i₀ + Δi, j₀ + Δj) = a² · Q(α - Δi, β - Δj).
  have dist_sq_formula : ∀ (Δi Δj : ℤ),
      dist p (isbellLatticePoint (i₀ + Δi) (j₀ + Δj)) ^ 2
        = a ^ 2 * ((α - Δi) ^ 2 + (α - Δi) * (β - Δj) + (β - Δj) ^ 2) := by
    intro Δi Δj
    rw [dist_point_lattice_sq_cart p (i₀ + Δi) (j₀ + Δj)]
    rw [hp0_eq, hp1_eq]
    push_cast
    -- Now both sides are pure algebra in s, t, a, sqrt 3, i₀, j₀, Δi, Δj.
    -- Use ring with the substitution sqrt3 * sqrt3 = 3.
    have hexpand :
        (s * a + t * (a / 2)
          - (((i₀ : ℝ) + (Δi : ℝ)) * a + ((j₀ : ℝ) + (Δj : ℝ)) * (a / 2))) ^ 2
        + (t * (a * Real.sqrt 3 / 2) - ((j₀ : ℝ) + (Δj : ℝ)) * (a * Real.sqrt 3 / 2)) ^ 2
        = a ^ 2 * ((s - i₀ - Δi) ^ 2 + (s - i₀ - Δi) * (t - j₀ - Δj)
            + (t - j₀ - Δj) ^ 2 / 4)
          + a ^ 2 * (Real.sqrt 3 * Real.sqrt 3) / 4 * (t - j₀ - Δj) ^ 2 := by ring
    rw [hexpand, hsq3]
    change a ^ 2 * ((s - (i₀ : ℝ) - Δi) ^ 2 +
        (s - (i₀ : ℝ) - Δi) * (t - (j₀ : ℝ) - Δj)
            + (t - (j₀ : ℝ) - Δj) ^ 2 / 4)
          + a ^ 2 * 3 / 4 * (t - (j₀ : ℝ) - Δj) ^ 2
        = a ^ 2 * (((s - (i₀ : ℝ)) - (Δi : ℝ)) ^ 2
            + ((s - (i₀ : ℝ)) - (Δi : ℝ)) * ((t - (j₀ : ℝ)) - (Δj : ℝ))
            + ((t - (j₀ : ℝ)) - (Δj : ℝ)) ^ 2)
    ring
  -- Goal-completing helper: given Δi, Δj and Q(α - Δi, β - Δj) ≤ 1/3,
  -- conclude dist ≤ a/√3.
  have finish : ∀ (Δi Δj : ℤ),
      ((α - Δi) ^ 2 + (α - Δi) * (β - Δj) + (β - Δj) ^ 2 ≤ 1 / 3) →
      dist p (isbellLatticePoint (i₀ + Δi) (j₀ + Δj)) ≤ a / Real.sqrt 3 := by
    intro Δi Δj hQ
    have hd_sq := dist_sq_formula Δi Δj
    -- a² · Q ≤ a² · (1/3), so dist² ≤ a²/3 = (a/√3)².
    have ha_sq_nn : 0 ≤ a ^ 2 := sq_nonneg _
    have hQ_nn : 0 ≤ (α - Δi) ^ 2 + (α - Δi) * (β - Δj) + (β - Δj) ^ 2 := by
      have h4Q : 4 * ((α - Δi) ^ 2 + (α - Δi) * (β - Δj) + (β - Δj) ^ 2)
          = (2 * (α - Δi) + (β - Δj)) ^ 2 + 3 * (β - Δj) ^ 2 := by ring
      nlinarith [sq_nonneg (2 * (α - Δi) + (β - Δj)), sq_nonneg (β - Δj), h4Q]
    have hd_sq_le : dist p (isbellLatticePoint (i₀ + Δi) (j₀ + Δj)) ^ 2
        ≤ a ^ 2 / 3 := by
      rw [hd_sq]
      nlinarith [ha_sq_nn, hQ, hQ_nn]
    -- (a/√3)² = a²/3.
    have h_rhs_sq : (a / Real.sqrt 3) ^ 2 = a ^ 2 / 3 := by
      rw [div_pow, Real.sq_sqrt (by norm_num : (3 : ℝ) ≥ 0)]
    have h_rhs_nn : 0 ≤ a / Real.sqrt 3 := by positivity
    have hd_nn : 0 ≤ dist p (isbellLatticePoint (i₀ + Δi) (j₀ + Δj)) := dist_nonneg
    have : dist p (isbellLatticePoint (i₀ + Δi) (j₀ + Δj)) ^ 2
        ≤ (a / Real.sqrt 3) ^ 2 := by rw [h_rhs_sq]; exact hd_sq_le
    exact abs_le_of_sq_le_sq' this h_rhs_nn |>.2
  obtain ⟨Δi, Δj, hQuadratic⟩ :=
    unitSquare_has_near_lattice_corner hα_lo hα_hi hβ_lo hβ_hi
  refine ⟨(i₀ + Δi, j₀ + Δj), ?_⟩
  exact finish Δi Δj hQuadratic

/-- The lattice coordinates of a lattice point within the Voronoi
    circumradius of `p`. Built via classical choice on
    `exists_lattice_point_within_circumradius`. -/
noncomputable def nearestLatticeIdx (p : R2) : ℤ × ℤ :=
  (exists_lattice_point_within_circumradius p).choose

/-- The defining property of `nearestLatticeIdx`: it lies within the
    Voronoi circumradius. -/
lemma nearestLatticeIdx_spec (p : R2) :
    dist p (isbellLatticePoint (nearestLatticeIdx p).1 (nearestLatticeIdx p).2)
      ≤ isbellLatticeStep / Real.sqrt 3 :=
  (exists_lattice_point_within_circumradius p).choose_spec

/-- Cast an integer residue modulo seven to the corresponding finite color. -/
noncomputable def toFin7 (n : ℤ) : Fin 7 :=
  (ZMod.finEquiv 7).symm (n : ZMod 7)

/-- The Isbell 7-coloring assigns to each point `p ∈ R²` the color
    `(i + 3·j) mod 7`, where `(i, j) = nearestLatticeIdx p` are the
    integer coordinates of a nearest lattice point. -/
noncomputable def isbellColor : R2 → Fin 7 :=
  fun p => toFin7 ((nearestLatticeIdx p).1 + 3 * (nearestLatticeIdx p).2)

/- ### The remaining geometric fact -/

/-- **(G1) Voronoi covering radius.** Every point of R² lies within
    distance `a/√3` of its assigned lattice point.

    Immediate corollary of `exists_lattice_point_within_circumradius`:
    by construction `nearestLatticeIdx` is *chosen* to satisfy this. -/
lemma dist_le_voronoi_circumradius (p : R2) :
    dist p (isbellLatticePoint (nearestLatticeIdx p).1 (nearestLatticeIdx p).2)
      ≤ isbellLatticeStep / Real.sqrt 3 :=
  nearestLatticeIdx_spec p

end HadwigerNelsonBounds

/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/


/-
# Separation of equally colored lattice points

This module proves the modular quadratic-form estimate that separates distinct
lattice points carrying the same residue color.
-/

namespace HadwigerNelsonBounds

open SimpleGraph

/-- **Number-theoretic core of (G2).** If `(Δi, Δj) ∈ ℤ²` is nonzero and
    `Δi + 3·Δj ≡ 0 (mod 7)`, then `Δi² + Δi·Δj + Δj² ≥ 7`.

    Proof outline: Let `Q := Δi² + Δi·Δj + Δj²`. Then
        4·Q = (2·Δi + Δj)² + 3·Δj².
    From `Δi + 3·Δj ≡ 0 (mod 7)`:
        `2·Δi + Δj = 2·(Δi + 3·Δj) − 5·Δj ≡ −5·Δj ≡ 2·Δj (mod 7)`,
    so `(2·Δi + Δj)² ≡ 4·Δj² (mod 7)`, hence
        `4·Q ≡ 4·Δj² + 3·Δj² = 7·Δj² ≡ 0 (mod 7)`.
    Since `gcd(4, 7) = 1`, `7 ∣ Q`.
    Also `Q ≥ 0` (sum of squares after `4·Q = (2·Δi+Δj)² + 3·Δj²`), and
    `Q = 0` would force `Δj = 0` and `2·Δi + Δj = 0`, hence
    `Δi = Δj = 0`, contradicting non-zeroness. So `Q > 0` and `7 ∣ Q`,
    giving `Q ≥ 7`. -/
private lemma sublattice_quadratic_form_ge_seven
    {di dj : ℤ} (hne : (di, dj) ≠ (0, 0))
    (hmod : (7 : ℤ) ∣ (di + 3 * dj)) :
    di ^ 2 + di * dj + dj ^ 2 ≥ 7 := by
  -- 7 divides di + 3·dj, so 2·di + dj = 2·(di + 3·dj) - 5·dj,
  -- and (2·di + dj)² ≡ 25·dj² ≡ 4·dj² (mod 7).
  -- Hence 4·Q = (2·di + dj)² + 3·dj² ≡ 7·dj² ≡ 0 (mod 7), so 7 | Q.
  have hQ_nonneg : 0 ≤ di ^ 2 + di * dj + dj ^ 2 := by
    have h4Q_form : 4 * (di ^ 2 + di * dj + dj ^ 2)
        = (2 * di + dj) ^ 2 + 3 * dj ^ 2 := by ring
    have : 0 ≤ (2 * di + dj) ^ 2 + 3 * dj ^ 2 := by positivity
    linarith [this, h4Q_form]
  -- 4·Q = (di + 3·dj)·(4·di − 8·dj) + 7·(4·dj²), so 7 | 4·Q.
  have hdvd_4Q : (7 : ℤ) ∣ (4 * (di ^ 2 + di * dj + dj ^ 2)) := by
    have hid : 4 * (di ^ 2 + di * dj + dj ^ 2)
        = (di + 3 * dj) * (4 * di - 8 * dj) + 7 * (4 * dj ^ 2) := by ring
    rw [hid]
    exact Dvd.dvd.add (Dvd.dvd.mul_right hmod _) (dvd_mul_right _ _)
  -- 7 coprime with 4, so 7 | Q.
  have hdvd_Q : (7 : ℤ) ∣ (di ^ 2 + di * dj + dj ^ 2) := by
    have h74 : IsCoprime (7 : ℤ) 4 := by decide
    exact h74.dvd_of_dvd_mul_left hdvd_4Q
  -- Q > 0 or Q = 0. If Q = 0, then (di, dj) = (0, 0).
  rcases hQ_nonneg.lt_or_eq with hpos | hzero
  · -- Q > 0 and 7 | Q, so Q ≥ 7.
    have : (7 : ℤ) ≤ di ^ 2 + di * dj + dj ^ 2 :=
      Int.le_of_dvd hpos hdvd_Q
    linarith
  · -- Q = 0. We show this contradicts hne.
    exfalso
    have hQ_eq : (di ^ 2 + di * dj + dj ^ 2) = 0 := hzero.symm
    have h4Q : 4 * (di ^ 2 + di * dj + dj ^ 2) = 0 := by linarith
    have h4Q_form : 4 * (di ^ 2 + di * dj + dj ^ 2)
        = (2 * di + dj) ^ 2 + 3 * dj ^ 2 := by ring
    rw [h4Q_form] at h4Q
    have h1 : (2 * di + dj) ^ 2 = 0 ∧ (3 : ℤ) * dj ^ 2 = 0 := by
      have hsq_nn : 0 ≤ (2 * di + dj) ^ 2 := sq_nonneg _
      have hd_nn : 0 ≤ (3 : ℤ) * dj ^ 2 := by positivity
      omega
    have hdj_zero : dj = 0 := by
      have : dj ^ 2 = 0 := by linarith [h1.2]
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    have hdi_zero : di = 0 := by
      have h0 : 2 * di + dj = 0 := by
        have hsq : (2 * di + dj) ^ 2 = 0 := h1.1
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
      omega
    apply hne
    simp [hdi_zero, hdj_zero]

/-- **(G2) Same-color lattice separation.** Two distinct lattice points
    with the same `(i + 3·j) mod 7` color are at Euclidean distance at
    least `a·√7`.

    Proof: if `(i, j) ≠ (i', j')` and `(i + 3·j) ≡ (i' + 3·j') (mod 7)`,
    then `(Δi, Δj) := (i − i', j − j')` is a nonzero integer vector
    with `Δi + 3·Δj ≡ 0 (mod 7)`. The Euclidean length squared of
    `Δi·v₁ + Δj·v₂` is
        a²·(Δi² + Δi·Δj + Δj²).
    By `sublattice_quadratic_form_ge_seven`, the integer quadratic form
    `Δi² + Δi·Δj + Δj² ≥ 7`, so squared distance ≥ 7·a², giving distance
    ≥ a·√7. -/
lemma dist_between_same_color_lattice_points
    {i j i' j' : ℤ} (hne : (i, j) ≠ (i', j'))
    (hsame : ((i + 3 * j) : ZMod 7) = ((i' + 3 * j') : ZMod 7)) :
    dist (isbellLatticePoint i j) (isbellLatticePoint i' j')
      ≥ isbellLatticeStep * Real.sqrt 7 := by
  -- Translate ZMod-7 equality to integer divisibility 7 ∣ ((i - i') + 3·(j - j')).
  have hmod : (7 : ℤ) ∣ ((i - i') + 3 * (j - j')) := by
    have hdiff_zero : (((i - i') + 3 * (j - j') : ℤ) : ZMod 7) = 0 := by
      push_cast
      -- Goal: (i : ZMod 7) - i' + 3 * (j - j') = 0
      -- From hsame : (i + 3*j) = (i' + 3*j') in ZMod 7, subtract.
      have hs : ((i : ZMod 7) + 3 * (j : ZMod 7)) - ((i' : ZMod 7) + 3 * (j' : ZMod 7)) = 0 := by
        rw [sub_eq_zero]; exact hsame
      linear_combination hs
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hdiff_zero
  -- Translate (i, j) ≠ (i', j') to ((i - i'), (j - j')) ≠ (0, 0).
  have hne' : (i - i', j - j') ≠ (0, 0) := by
    intro h
    apply hne
    have h1 : i - i' = 0 := (Prod.mk.injEq _ _ _ _).mp h |>.1
    have h2 : j - j' = 0 := (Prod.mk.injEq _ _ _ _).mp h |>.2
    have : i = i' := by omega
    have : j = j' := by omega
    simp_all
  -- Apply the number-theoretic core.
  have hQ_ge_7 : (7 : ℤ) ≤ (i - i') ^ 2 + (i - i') * (j - j') + (j - j') ^ 2 :=
    sublattice_quadratic_form_ge_seven hne' hmod
  have hQ_ge_7_real :
      (7 : ℝ) ≤
        ((i : ℝ) - i') ^ 2 +
          ((i : ℝ) - i') * ((j : ℝ) - j') +
          ((j : ℝ) - j') ^ 2 := by
    have h1 :
        ((7 : ℤ) : ℝ) ≤
          (((i - i') ^ 2 + (i - i') * (j - j') +
            (j - j') ^ 2 : ℤ) : ℝ) := by
      exact_mod_cast hQ_ge_7
    have hcast : (((i - i') ^ 2 + (i - i') * (j - j') + (j - j') ^ 2 : ℤ) : ℝ)
        = ((i : ℝ) - i') ^ 2 + ((i : ℝ) - i') * ((j : ℝ) - j') + ((j : ℝ) - j') ^ 2 := by
      push_cast; ring
    rw [hcast] at h1
    exact_mod_cast h1
  -- Squared distance equals a²·Q.
  have hdist_sq := isbellLatticePoint_dist_sq i j i' j'
  -- Distance is nonneg.
  have hdist_nn : (0 : ℝ) ≤ dist (isbellLatticePoint i j) (isbellLatticePoint i' j') :=
    dist_nonneg
  -- isbellLatticeStep ≥ 0.
  have ha_nn : (0 : ℝ) ≤ isbellLatticeStep := by unfold isbellLatticeStep; norm_num
  -- √7 ≥ 0.
  have hsqrt7_nn : (0 : ℝ) ≤ Real.sqrt 7 := Real.sqrt_nonneg _
  -- The squared bound.
  have hsq_bound :
      (isbellLatticeStep * Real.sqrt 7) ^ 2
        ≤ dist (isbellLatticePoint i j) (isbellLatticePoint i' j') ^ 2 := by
    rw [hdist_sq]
    have hsq7 : Real.sqrt 7 * Real.sqrt 7 = 7 := Real.mul_self_sqrt (by norm_num)
    have hsq7_eq : (isbellLatticeStep * Real.sqrt 7) ^ 2 = isbellLatticeStep ^ 2 * 7 := by
      have : (isbellLatticeStep * Real.sqrt 7) ^ 2
          = isbellLatticeStep ^ 2 * (Real.sqrt 7 * Real.sqrt 7) := by ring
      rw [this, hsq7]
    rw [hsq7_eq]
    have hstep_sq_nn : (0 : ℝ) ≤ isbellLatticeStep ^ 2 := sq_nonneg _
    nlinarith [hQ_ge_7_real, hstep_sq_nn]
  -- Square root of the squared bound: since both sides are nonneg, squared inequality
  -- transfers to the inequality on the original values.
  have h_step7_nn : 0 ≤ isbellLatticeStep * Real.sqrt 7 := by positivity
  have hkey : isbellLatticeStep * Real.sqrt 7
      ≤ dist (isbellLatticePoint i j) (isbellLatticePoint i' j') := by
    -- Want: a·√7 ≤ dist. Have: (a·√7)² ≤ dist², and both ≥ 0.
    -- Use abs_le_of_sq_le_sq.
    nlinarith [hsq_bound, hdist_nn, h_step7_nn,
      sq_nonneg (dist (isbellLatticePoint i j) (isbellLatticePoint i' j')
        - isbellLatticeStep * Real.sqrt 7),
      sq_nonneg (dist (isbellLatticePoint i j) (isbellLatticePoint i' j')
        + isbellLatticeStep * Real.sqrt 7)]
  linarith [hkey]

end HadwigerNelsonBounds

/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/


/-
# Isbell's seven-coloring

This module proves the numerical gap estimates, constructs the plane coloring,
and establishes the seven-color upper bound.
-/

namespace HadwigerNelsonBounds

open SimpleGraph

/- ### Numerical inequalities -/

/-- `0 < √3`. -/
private lemma sqrt_three_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)

/-- `0 < √7`. -/
private lemma sqrt_seven_pos : 0 < Real.sqrt 7 := Real.sqrt_pos.mpr (by norm_num)

/-- `√3 < 2`. -/
private lemma sqrt_three_lt_two : Real.sqrt 3 < 2 := by
  have h2 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hpos : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
  nlinarith [h2, hpos]

/-- The within-tile diameter `2·(a/√3) = √3/2` is `< 1`. -/
lemma isbell_voronoi_diameter_lt_one :
    2 * (isbellLatticeStep / Real.sqrt 3) < 1 := by
  unfold isbellLatticeStep
  -- Reduce: 2·(3/4)/√3 = 3/(2·√3) = √3/2. Show √3/2 < 1, i.e. √3 < 2.
  have hs3 : 0 < Real.sqrt 3 := sqrt_three_pos
  have hsq : Real.sqrt 3 * Real.sqrt 3 = 3 := sqrt_three_mul_self
  have hlt : Real.sqrt 3 < 2 := sqrt_three_lt_two
  -- Rationalizing gives 2·(3/4)/√3 = √3/2, which is less than one.
  have key : 2 * (3 / 4 / Real.sqrt 3) = Real.sqrt 3 / 2 := by
    have : (3 : ℝ) / 4 / Real.sqrt 3 = 3 / (4 * Real.sqrt 3) := by ring
    rw [this]
    field_simp
    nlinarith [hsq]
  rw [key]
  linarith [hlt]

/-- The same-color spacing `a·(√7 − 2/√3) > 1` for `a = 3/4`. -/
lemma isbell_same_color_min_gt_one :
    isbellLatticeStep * (Real.sqrt 7 - 2 / Real.sqrt 3) > 1 := by
  unfold isbellLatticeStep
  -- It is enough to prove 3√7 > 4 + 2√3 after clearing denominators.
  -- Square both sides (both positive):
  --         (3√7)² > (4 + 2√3)²
  --         63 > 16 + 16√3 + 12 = 28 + 16√3
  --         35 > 16√3
  --         (35)² > (16√3)²
  --         1225 > 768                                              ✓
  have hs3 : 0 < Real.sqrt 3 := sqrt_three_pos
  have hs7 : 0 < Real.sqrt 7 := sqrt_seven_pos
  have hsq3 : Real.sqrt 3 * Real.sqrt 3 = 3 := sqrt_three_mul_self
  have hsq7 : Real.sqrt 7 * Real.sqrt 7 = 7 :=
    Real.mul_self_sqrt (by norm_num)
  -- Show 2/√3 = (2√3)/3
  have h2div3 : (2 : ℝ) / Real.sqrt 3 = 2 * Real.sqrt 3 / 3 := by
    field_simp
    nlinarith [hsq3]
  rw [h2div3]
  -- After substitution, multiplying by four reduces the goal to
  -- 3·√7 − 2·√3 > 4.
  -- We show 3√7 − 2√3 > 4 via:  35² > 768·1, i.e. (35)² > (16√3)²,
  -- i.e. 1225 > 768, hence 35 > 16√3, hence 63 - 28 > 16√3,
  -- i.e. 63 > 28 + 16√3 = (4 + 2√3)², so 3√7 = √63 > 4 + 2√3.
  -- Use nlinarith with all the sqrt facts.
  have hsq35 : (35 : ℝ)^2 = 1225 := by norm_num
  have h16s3 : (16 * Real.sqrt 3)^2 = 16^2 * 3 := by
    have : (16 * Real.sqrt 3)^2 = 16^2 * (Real.sqrt 3 * Real.sqrt 3) := by ring
    rw [this, hsq3]
  have h35_gt : 35 > 16 * Real.sqrt 3 := by
    have hsq_le : (16 * Real.sqrt 3)^2 < (35 : ℝ)^2 := by
      rw [h16s3, hsq35]; norm_num
    have h16s3_pos : 0 < 16 * Real.sqrt 3 := by positivity
    nlinarith [hsq_le, h16s3_pos]
  -- From 35 > 16√3, derive 3√7 > 4 + 2√3 by squaring once more.
  -- (3√7)² = 63, (4 + 2√3)² = 16 + 16√3 + 12 = 28 + 16√3.
  -- 63 - 28 = 35 > 16√3 ⟹ 63 > 28 + 16√3 = (4 + 2√3)².
  have hsq3_pos : 0 < 4 + 2 * Real.sqrt 3 := by positivity
  have hsq_4_2s3 : (4 + 2 * Real.sqrt 3)^2 = 28 + 16 * Real.sqrt 3 := by
    have : (4 + 2 * Real.sqrt 3)^2
        = 16 + 16 * Real.sqrt 3 + 4 * (Real.sqrt 3 * Real.sqrt 3) := by ring
    rw [this, hsq3]; ring
  have h_3s7_sq : (3 * Real.sqrt 7)^2 = 63 := by
    have : (3 * Real.sqrt 7)^2 = 9 * (Real.sqrt 7 * Real.sqrt 7) := by ring
    rw [this, hsq7]; norm_num
  have h_3s7_gt : 3 * Real.sqrt 7 > 4 + 2 * Real.sqrt 3 := by
    have hsq_lt : (4 + 2 * Real.sqrt 3)^2 < (3 * Real.sqrt 7)^2 := by
      rw [hsq_4_2s3, h_3s7_sq]; linarith [h35_gt]
    have h3s7_pos : 0 < 3 * Real.sqrt 7 := by positivity
    nlinarith [hsq_lt, hsq3_pos, h3s7_pos]
  -- Conclude from the cleared-denominator inequality.
  nlinarith [h_3s7_gt, hs3, hs7]

/- ### The proper-coloring theorem -/

/-- **The Isbell coloring is proper.** Two points at unit distance receive
    different colors. -/
theorem isbell_isProperColoring :
    ∀ {p q : R2}, unitDistanceGraph.Adj p q → isbellColor p ≠ isbellColor q := by
  intro p q hadj hsame
  -- Unfold adjacency to `dist p q = 1`.
  rw [unitDistanceGraph_adj] at hadj
  obtain ⟨_hne, hdist⟩ := hadj
  have hpq : dist p q = 1 := by
    rcases hdist with h | h
    · exact h
    · simpa [_root_.dist_comm] using h
  -- Unpack lattice indices.
  set ip := (nearestLatticeIdx p).1 with hip_def
  set jp := (nearestLatticeIdx p).2 with hjp_def
  set iq := (nearestLatticeIdx q).1 with hiq_def
  set jq := (nearestLatticeIdx q).2 with hjq_def
  -- `isbellColor` equality lifts to ZMod 7 equality on `i + 3·j`.
  have hcolor : (((ip : ZMod 7)) + 3 * ((jp : ZMod 7))) =
                (((iq : ZMod 7)) + 3 * ((jq : ZMod 7))) := by
    have h' : ((ip + 3 * jp : ℤ) : ZMod 7) =
        ((iq + 3 * jq : ℤ) : ZMod 7) := by
      have transformed := congrArg (ZMod.finEquiv 7) hsame
      simpa [isbellColor, toFin7, hip_def, hjp_def, hiq_def, hjq_def] using
        transformed
    push_cast at h'
    exact h'
  -- Voronoi cell bounds for p and q.
  have hp_close : dist p (isbellLatticePoint ip jp)
      ≤ isbellLatticeStep / Real.sqrt 3 := dist_le_voronoi_circumradius p
  have hq_close : dist q (isbellLatticePoint iq jq)
      ≤ isbellLatticeStep / Real.sqrt 3 := dist_le_voronoi_circumradius q
  -- Case split: same cell vs different cells.
  by_cases hsame_cell : (ip, jp) = (iq, jq)
  · -- Case 1: same cell — within-cell diameter < 1 contradicts dist = 1.
    have hp_eq : isbellLatticePoint ip jp = isbellLatticePoint iq jq := by
      have h1 : ip = iq := by
        exact (Prod.mk.injEq _ _ _ _).mp hsame_cell |>.1
      have h2 : jp = jq := by
        exact (Prod.mk.injEq _ _ _ _).mp hsame_cell |>.2
      rw [h1, h2]
    have htri : dist p q
        ≤ dist p (isbellLatticePoint ip jp) + dist q (isbellLatticePoint iq jq) := by
      calc dist p q
          ≤ dist p (isbellLatticePoint iq jq) + dist (isbellLatticePoint iq jq) q :=
            dist_triangle _ _ _
        _ = dist p (isbellLatticePoint iq jq) + dist q (isbellLatticePoint iq jq) := by
            rw [dist_comm (isbellLatticePoint iq jq) q]
        _ = dist p (isbellLatticePoint ip jp) + dist q (isbellLatticePoint iq jq) := by
            rw [hp_eq]
    have hbound : dist p q ≤ 2 * (isbellLatticeStep / Real.sqrt 3) := by
      linarith [htri, hp_close, hq_close]
    have hlt : dist p q < 1 := lt_of_le_of_lt hbound isbell_voronoi_diameter_lt_one
    linarith [hlt, hpq]
  · -- Case 2: different cells, same color — same-color spacing contradicts dist = 1.
    have hne : (ip, jp) ≠ (iq, jq) := hsame_cell
    have hfar : dist (isbellLatticePoint ip jp) (isbellLatticePoint iq jq)
        ≥ isbellLatticeStep * Real.sqrt 7 :=
      dist_between_same_color_lattice_points hne hcolor
    -- Reverse triangle: dist(centerₚ, center_q) ≤ |centerₚ - p| + |p - q| + |q - center_q|
    have hrtri : dist (isbellLatticePoint ip jp) (isbellLatticePoint iq jq)
        ≤ dist (isbellLatticePoint ip jp) p
          + dist p q
          + dist q (isbellLatticePoint iq jq) := by
      have h1 : dist (isbellLatticePoint ip jp) (isbellLatticePoint iq jq)
          ≤ dist (isbellLatticePoint ip jp) p + dist p (isbellLatticePoint iq jq) :=
        dist_triangle _ _ _
      have h2 : dist p (isbellLatticePoint iq jq)
          ≤ dist p q + dist q (isbellLatticePoint iq jq) :=
        dist_triangle _ _ _
      linarith
    have hp_close' : dist (isbellLatticePoint ip jp) p
        ≤ isbellLatticeStep / Real.sqrt 3 := by
      rw [_root_.dist_comm]; exact hp_close
    have hbound : isbellLatticeStep * Real.sqrt 7
        ≤ 2 * (isbellLatticeStep / Real.sqrt 3) + dist p q := by
      linarith [hfar, hrtri, hp_close', hq_close]
    have hgap : isbellLatticeStep * Real.sqrt 7 - 2 * (isbellLatticeStep / Real.sqrt 3)
        = isbellLatticeStep * (Real.sqrt 7 - 2 / Real.sqrt 3) := by ring
    have hgt_one : isbellLatticeStep * Real.sqrt 7
        - 2 * (isbellLatticeStep / Real.sqrt 3) > 1 := by
      rw [hgap]; exact isbell_same_color_min_gt_one
    have hgt : dist p q > 1 := by linarith
    linarith [hgt, hpq]

/-- Bundle the Isbell witness into a `SimpleGraph.Coloring`. -/
noncomputable def isbellColoring : unitDistanceGraph.Coloring (Fin 7) :=
  Coloring.mk isbellColor isbell_isProperColoring

/-- **Upper bound — χ(R²) ≤ 7.** The unit-distance graph on R² is
    7-colorable. -/
theorem chromaticNumber_le_seven :
    unitDistanceGraph.Colorable 7 :=
  ⟨isbellColoring⟩

end HadwigerNelsonBounds

namespace Erdos508Aux

open SimpleGraph

/-- The exact graph used in the conjecture, without importing its admitted statement. -/
abbrev planeGraph : SimpleGraph
    (Set.univ : Set (EuclideanSpace ℝ (Fin 2))) :=
  UnitDistancePlaneGraph Set.univ

/-- Forgetting the `Set.univ` subtype identifies the specified graph with the graph
used by the independent Isbell construction. -/
def planeToIsbell : planeGraph →g HadwigerNelsonBounds.unitDistanceGraph where
  toFun p := p.val
  map_rel' := by
    intro p q hpq
    change dist p.val q.val = 1 at hpq
    apply (HadwigerNelsonBounds.unitDistanceGraph_adj p.val q.val).mpr
    refine ⟨?_, Or.inl hpq⟩
    intro heq
    rw [heq, _root_.dist_self] at hpq
    norm_num at hpq

/-- A complete seven-coloring of the exact graph in Spec.lean. -/
theorem plane_colorable_seven : planeGraph.Colorable 7 :=
  Colorable.of_hom planeToIsbell HadwigerNelsonBounds.chromaticNumber_le_seven

/-- The verified upper bound for the exact specified graph. -/
theorem plane_chromaticNumber_le_seven : planeGraph.chromaticNumber ≤ 7 :=
  plane_colorable_seven.chromaticNumber_le

/-- With the upper bound proved independently, the missing conjectural part is
precisely non-six-colorability. This lemma does not prove that missing part. -/
theorem plane_eq_seven_iff_not_colorable_six :
    planeGraph.chromaticNumber = 7 ↔ ¬ planeGraph.Colorable 6 := by
  have h : planeGraph.chromaticNumber = 7 ↔
      planeGraph.Colorable 7 ∧ ¬ planeGraph.Colorable 6 := by
    simpa using
      (SimpleGraph.chromaticNumber_eq_iff_colorable_not_colorable
        (G := planeGraph) (n := 6))
  simpa [plane_colorable_seven] using h

/-- The disproof route is precisely a genuine unrestricted six-coloring. -/
theorem plane_not_eq_seven_iff_colorable_six :
    ¬ planeGraph.chromaticNumber = 7 ↔ planeGraph.Colorable 6 := by
  classical
  rw [plane_eq_seven_iff_not_colorable_six, not_not]

/-- An exact unit-edge realization need not be induced or injective for transferring
non-colorability. No such non-six witness is supplied by this definition. -/
def unitRealizationHom {V : Type*} {G : SimpleGraph V}
    (f : V → EuclideanSpace ℝ (Fin 2))
    (hf : ∀ u v, G.Adj u v → dist (f u) (f v) = 1) : G →g planeGraph where
  toFun v := ⟨f v, Set.mem_univ _⟩
  map_rel' := by
    intro u v huv
    exact hf u v huv

/-- A sound conditional route from an actual non-six unit graph to the conjecture.
Its non-six-colorability hypothesis remains entirely unproved here. -/
theorem plane_eq_seven_of_unit_realization_not_six
    {V : Type*} {G : SimpleGraph V}
    (f : V → EuclideanSpace ℝ (Fin 2))
    (hf : ∀ u v, G.Adj u v → dist (f u) (f v) = 1)
    (hn : ¬ G.Colorable 6) : planeGraph.chromaticNumber = 7 := by
  apply plane_eq_seven_iff_not_colorable_six.mpr
  intro hp
  exact hn (Colorable.of_hom (unitRealizationHom f hf) hp)

end Erdos508Aux

namespace Erdos508Aux

open SimpleGraph

/-- Finite-color compactness, specialized to colorings rather than arbitrary graph
homomorphisms. The forward direction is restriction; the reverse direction is the
existing Mathlib compactness theorem. -/
theorem colorable_iff_all_finite_subgraphs {V : Type*} (G : SimpleGraph V) (n : ℕ) :
    G.Colorable n ↔
      ∀ H : G.Subgraph, H.verts.Finite → H.coe.Colorable n := by
  classical
  constructor
  · intro h H _
    exact Colorable.of_hom H.hom h
  · intro h
    exact SimpleGraph.nonempty_hom_of_forall_finite_subgraph_hom
      (fun H hf => Classical.choice (h H hf))

/-- The exact conjecture has a finite witness if and only if it is true. This is
not the construction of such a witness: the existential statement is unresolved. -/
theorem plane_eq_seven_iff_finite_non_six :
    planeGraph.chromaticNumber = 7 ↔
      ∃ H : planeGraph.Subgraph, H.verts.Finite ∧ ¬ H.coe.Colorable 6 := by
  classical
  rw [plane_eq_seven_iff_not_colorable_six,
    colorable_iff_all_finite_subgraphs planeGraph 6]
  simp only [not_forall, exists_prop]

/-- Conversely, the exact negation would follow from six-colorability of every
finite subgraph. No uniform six-colorability theorem is asserted here. -/
theorem plane_not_eq_seven_iff_all_finite_six :
    ¬ planeGraph.chromaticNumber = 7 ↔
      ∀ H : planeGraph.Subgraph, H.verts.Finite → H.coe.Colorable 6 := by
  rw [plane_not_eq_seven_iff_colorable_six,
    colorable_iff_all_finite_subgraphs planeGraph 6]

end Erdos508Aux
