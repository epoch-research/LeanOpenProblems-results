import FormalConjecturesUtil

/-!
A limitation of directly polarizing the scalar quadratic physical-domain
kernel. This file does not prove or disprove the conjecture in Spec.lean.
-/

namespace PolarizedQuadraticKernel

noncomputable def entry {ι : Type*} (x : ℝ) (a r : ι → ℝ) (i j : ι) : ℝ :=
  x * a i * a j - a i * r j - r i * a j

/-- The determinant of any two-coordinate restriction is nonpositive,
independently of the value of the real endpoint. -/
theorem two_coordinate_determinant {ι : Type*} (x : ℝ) (a r : ι → ℝ) (i j : ι) :
    entry x a r i i * entry x a r j j -
        entry x a r i j * entry x a r j i =
      -(a i * r j - a j * r i)^2 := by
  unfold entry
  ring

theorem two_coordinate_determinant_nonpos {ι : Type*}
    (x : ℝ) (a r : ι → ℝ) (i j : ι) :
    entry x a r i i * entry x a r j j -
        entry x a r i j * entry x a r j i ≤ 0 := by
  rw [two_coordinate_determinant]
  exact neg_nonpos.mpr (sq_nonneg _)

/-- Nonnegative two-coordinate determinants force all wedges to vanish. -/
theorem wedge_zero {ι : Type*} (x : ℝ) (a r : ι → ℝ)
    (h : ∀ i j, 0 ≤ entry x a r i i * entry x a r j j -
        entry x a r i j * entry x a r j i) (i j : ι) :
    a i * r j - a j * r i = 0 := by
  have hh := h i j
  rw [two_coordinate_determinant] at hh
  have hs : (a i * r j - a j * r i)^2 = 0 :=
    le_antisymm (by linarith) (sq_nonneg _)
  exact (sq_eq_zero_iff).mp hs

/-- If one constant component is nonzero, every boundary component has
that same proportionality factor. -/
theorem boundary_proportional {ι : Type*} (x : ℝ) (a r : ι → ℝ)
    (h : ∀ i j, 0 ≤ entry x a r i i * entry x a r j j -
        entry x a r i j * entry x a r j i)
    (k : ι) (hk : a k ≠ 0) (i : ι) :
    r i = (r k / a k) * a i := by
  have hw := wedge_zero x a r h k i
  apply (mul_left_cancel₀ hk)
  field_simp
  nlinarith only [hw]

/-- Consequently this particular pencil is a scalar multiple of a single
outer product, or is zero. This is not a statement about arbitrary kernel
matrix constructions. -/
theorem outer_product_or_zero {ι : Type*} (x : ℝ) (a r : ι → ℝ)
    (h : ∀ i j, 0 ≤ entry x a r i i * entry x a r j j -
        entry x a r i j * entry x a r j i) :
    (∀ i j, entry x a r i j = 0) ∨
      ∃ c : ℝ, ∀ i j, entry x a r i j = c * a i * a j := by
  classical
  by_cases ha : ∀ i, a i = 0
  · left
    intro i j
    simp [entry, ha]
  · push_neg at ha
    obtain ⟨k, hk⟩ := ha
    right
    refine ⟨x - 2 * (r k / a k), ?_⟩
    intro i j
    unfold entry
    rw [boundary_proportional x a r h k hk i,
      boundary_proportional x a r h k hk j]
    ring

/-- Positive semidefiniteness supplies the required minor inequalities. -/
theorem posSemidef_outer_product_or_zero {ι : Type*}
    (x : ℝ) (a r : ι → ℝ)
    (h : Matrix.PosSemidef (entry x a r)) :
    (∀ i j, entry x a r i j = 0) ∨
      ∃ c : ℝ, ∀ i j, entry x a r i j = c * a i * a j := by
  apply outer_product_or_zero x a r
  intro i j
  have hm := (h.submatrix (![i, j] : Fin 2 → ι)).det_nonneg
  simpa [Matrix.det_fin_two, Matrix.submatrix_apply] using hm

/-- Already a two-dimensional directly polarized pencil cannot be
positive definite. -/
theorem not_posDef_two (x : ℝ) (a r : Fin 2 → ℝ) :
    ¬ Matrix.PosDef (entry x a r) := by
  intro h
  have hp := h.det_pos
  rw [Matrix.det_fin_two] at hp
  exact (not_lt_of_ge (two_coordinate_determinant_nonpos x a r 0 1)) hp

end PolarizedQuadraticKernel

#print axioms PolarizedQuadraticKernel.two_coordinate_determinant
#print axioms PolarizedQuadraticKernel.outer_product_or_zero
#print axioms PolarizedQuadraticKernel.posSemidef_outer_product_or_zero
#print axioms PolarizedQuadraticKernel.not_posDef_two
