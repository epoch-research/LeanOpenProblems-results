import FormalConjecturesUtil

/-!
# A backward clipping inequality for finite positive measures

These are auxiliary inequalities only. They do not settle the odd covering
conjecture, nor establish the proposed joint digit-compression comparison.
-/
namespace Erdos7Backward
open scoped BigOperators
set_option maxHeartbeats 1000000

/-- The affine backward step, separated from any unproved comparison operator.
`hfuture` is the implication supplied by a hypothetical remaining cover, and
`hcomparison` must be established independently for the clipped future test. -/
theorem clipped_step {Ω Ψ : Type*} [Fintype Ω] [Fintype Ψ]
    (μ : Ω → ℚ) (ν : Ψ → ℚ) (hν : ∀ y, 0 ≤ ν y)
    (F : Ψ → ℚ) (loss T : Ω → ℚ) (L ell : ℚ)
    (hell : ell ≤ 1)
    (hmass : (∑ y, ν y) = (∑ x, μ x) - L)
    (hfuture : (∑ y, ν y) ≤ ∑ y, ν y * F y)
    (hloss : L ≤ ∑ x, μ x * loss x)
    (hcomparison : (∑ y, ν y * max (F y - ell) 0) ≤ ∑ x, μ x * T x) :
    (∑ x, μ x) ≤ ∑ x, μ x * (ell + (1 - ell) * loss x + T x) := by
  have hclip : (∑ y, ν y * F y) ≤ ell * (∑ y, ν y) + ∑ x, μ x * T x := by
    calc
      _ ≤ ∑ y, ν y * (ell + max (F y - ell) 0) := by
        apply Finset.sum_le_sum
        intro y _
        apply mul_le_mul_of_nonneg_left _ (hν y)
        have hh := le_max_left (F y - ell) (0 : ℚ)
        linarith
      _ = ell * (∑ y, ν y) + ∑ y, ν y * max (F y - ell) 0 := by
        simp only [mul_add, Finset.sum_add_distrib]
        rw [← Finset.sum_mul]
        ring
      _ ≤ _ := add_le_add le_rfl hcomparison
  have hmain := hfuture.trans hclip
  rw [hmass] at hmain
  have hl := mul_le_mul_of_nonneg_left hloss (sub_nonneg.mpr hell)
  have heq : (∑ x, μ x * (ell + (1 - ell) * loss x + T x)) =
      ell * (∑ x, μ x) + (1 - ell) * (∑ x, μ x * loss x) + ∑ x, μ x * T x := by
    simp only [mul_add, Finset.sum_add_distrib]
    simp_rw [show ∀ x, μ x * ((1 - ell) * loss x) =
      (1 - ell) * (μ x * loss x) by intro x; ring]
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    ring
  rw [heq]
  nlinarith

/-- Constant clipping preserves the four-number supermodular inequality,
provided the two middle values lie between the extreme values. -/
theorem clipped_four_point (a b c d ell : ℚ)
    (hab : a ≤ b) (hac : a ≤ c) (hbd : b ≤ d) (hcd : c ≤ d)
    (hs : b + c ≤ a + d) :
    max (b - ell) 0 + max (c - ell) 0 ≤
      max (a - ell) 0 + max (d - ell) 0 := by
  by_cases ha : ell ≤ a
  · rw [max_eq_left (by linarith : 0 ≤ a - ell),
      max_eq_left (by linarith : 0 ≤ b - ell),
      max_eq_left (by linarith : 0 ≤ c - ell),
      max_eq_left (by linarith : 0 ≤ d - ell)]
    linarith
  · rw [max_eq_right (by linarith : a - ell ≤ 0)]
    by_cases hb : ell ≤ b <;> by_cases hc : ell ≤ c
    · rw [max_eq_left (by linarith : 0 ≤ b - ell),
        max_eq_left (by linarith : 0 ≤ c - ell),
        max_eq_left (by linarith : 0 ≤ d - ell)]
      linarith
    · rw [max_eq_left (by linarith : 0 ≤ b - ell),
        max_eq_right (by linarith : c - ell ≤ 0),
        max_eq_left (by linarith : 0 ≤ d - ell)]
      linarith
    · rw [max_eq_right (by linarith : b - ell ≤ 0),
        max_eq_left (by linarith : 0 ≤ c - ell),
        max_eq_left (by linarith : 0 ≤ d - ell)]
      linarith
    · rw [max_eq_right (by linarith : b - ell ≤ 0),
        max_eq_right (by linarith : c - ell ≤ 0)]
      simpa only [zero_add] using le_max_right (d - ell) (0 : ℚ)

/-- In particular, a monotone supermodular function on any lattice remains
supermodular after subtracting a constant and clipping at zero. -/
theorem clipped_supermodular {α : Type*} [Lattice α] (F : α → ℚ)
    (hmono : Monotone F)
    (hF : ∀ x y, F x + F y ≤ F (x ⊓ y) + F (x ⊔ y)) (ell : ℚ) :
    ∀ x y, max (F x - ell) 0 + max (F y - ell) 0 ≤
      max (F (x ⊓ y) - ell) 0 + max (F (x ⊔ y) - ell) 0 := by
  intro x y
  exact clipped_four_point _ _ _ _ ell
    (hmono inf_le_left) (hmono inf_le_right)
    (hmono le_sup_left) (hmono le_sup_right) (hF x y)

/-- Scalar convexity is also preserved by clipping. Applying this to each
coordinate gives the coordinatewise-convex part of the proposed test cone. -/
theorem clipped_convex (F : ℚ → ℚ) (hF : ConvexOn ℚ Set.univ F) (ell : ℚ) :
    ConvexOn ℚ Set.univ (fun x => max (F x - ell) 0) := by
  simpa only [sub_eq_add_neg] using
    (hF.add_const (-ell)).sup (convexOn_const 0 convex_univ)

#print axioms clipped_step
#print axioms clipped_four_point
#print axioms clipped_supermodular
#print axioms clipped_convex
end Erdos7Backward
