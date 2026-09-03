import FormalConjecturesUtil

/-!
An obstruction to an exact multivariate extension of scalar diagonal splitting.
This is about a proposed proof method, NOT about existence of odd covers.
-/
namespace Erdos7MultitypeDiagonalObstruction

/-- A separable majorant of the positive part of `x+y-1` on the unit square
has uniform additive error at least one half. No regularity assumptions on
its one-variable summands are needed. -/
theorem half_le_separable_error (b ε : ℝ) (f g : ℝ → ℝ)
    (hl : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      max 0 (x+y-1) ≤ b+f x+g y)
    (hu : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      b+f x+g y ≤ max 0 (x+y-1)+ε) :
    (1 : ℝ)/2 ≤ ε := by
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num
  have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num
  have h00 := hl 0 h0 0 h0
  have h11 := hl 1 h1 1 h1
  have h01 := hu 0 h0 1 h1
  have h10 := hu 1 h1 0 h0
  norm_num at h00 h11 h01 h10
  linarith

/-- The exact two-variable diagonal envelope cannot be split into a constant
and separate tests, even without requiring convexity or monotonicity. -/
theorem no_exact_separable_split :
    ¬ ∃ (b : ℝ) (f g : ℝ → ℝ),
      (∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
        0 ≤ b+f x+g y) ∧
      (∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
        x+y-1 ≤ b+f x+g y) ∧
      (∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
        b+f x+g y ≤ max 0 (x+y-1)) := by
  rintro ⟨b,f,g,h0,h1,hu⟩
  have hh := half_le_separable_error b 0 f g
    (fun x hx y hy => max_le (h0 x hx y hy) (h1 x hx y hy))
    (fun x hx y hy => by simpa using hu x hx y hy)
  norm_num at hh

/-- The lower bound is sharp, already among affine monotone summands. -/
theorem affine_half_error (x y : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    max 0 (x+y-1) ≤ x/2+y/2 ∧
      x/2+y/2 ≤ max 0 (x+y-1)+(1 : ℝ)/2 := by
  constructor
  · apply max_le <;> linarith [hx.1,hx.2,hy.1,hy.2]
  · have h0 : (0 : ℝ) ≤ max 0 (x+y-1) := le_max_left _ _
    have h1 : x+y-1 ≤ max 0 (x+y-1) := le_max_right _ _
    linarith

#print axioms half_le_separable_error
#print axioms no_exact_separable_split
#print axioms affine_half_error
end Erdos7MultitypeDiagonalObstruction
