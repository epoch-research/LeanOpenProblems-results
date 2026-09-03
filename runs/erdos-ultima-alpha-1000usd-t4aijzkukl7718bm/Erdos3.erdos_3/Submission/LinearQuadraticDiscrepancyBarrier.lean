import Submission.QuadraticSquareDiscrepancy

/-! A linear factor satisfies the quadratic third-difference relation but not
the pure-quadratic joint distribution hypothesis. This rules out dropping that
hypothesis in the new transfer criterion. It is not a counterexample to Erdos3. -/
namespace Erdos3LinearQuadraticDiscrepancyBarrier
open Finset Erdos3QuadraticSquareDiscrepancy
open scoped BigOperators Classical
set_option maxHeartbeats 2000000

variable {F : Type*} [Field F] [Fintype F]

lemma linear_three_characters (χ : AddChar F ℂ) (x d : F) :
    χ x*((χ^2)⁻¹) (x+d)*χ (x+2*d) = 1 := by
  calc
    _ = χ (x+2 • (-(x+d))+(x+2*d)) := by
      simp only [AddChar.inv_apply,AddChar.pow_apply,χ.map_add_eq_mul,χ.map_nsmul_eq_pow]
    _ = 1 := by
      rw [show x+2 • (-(x+d))+(x+2*d) = 0 by simp only [nsmul_eq_mul]; ring,
        χ.map_zero_eq_one]

/-- The triple distribution of a linear factor has discrepancy exactly one
from independent coordinates, despite vanishing quadratic third differences. -/
theorem linear_discrepancy_one (χ : AddChar F ℂ) (hχ : χ ≠ 1) :
    ‖(𝔼 x : F, 𝔼 d : F, χ x*((χ^2)⁻¹) (x+d)*χ (x+2*d))-
      (𝔼 p : F × F × F, χ p.1*((χ^2)⁻¹) p.2.1*χ p.2.2)‖ = 1 := by
  have h0 : (𝔼 x : F, χ x) = 0 := AddChar.expect_eq_zero_iff_ne_zero.mpr hχ
  simp only [linear_three_characters,Fintype.expect_const,independent_character_mean,
    h0,zero_mul,sub_zero,norm_one]

theorem not_linear_discrepancy_small (χ : AddChar F ℂ) (hχ : χ ≠ 1)
    {ε : ℝ} (hε : ε < 1) :
    ¬ (∀ χ₀ χ₁ χ₂ : AddChar F ℂ,
      ‖(𝔼 x : F, 𝔼 d : F, χ₀ x*χ₁ (x+d)*χ₂ (x+2*d))-
        (𝔼 p : F × F × F, χ₀ p.1*χ₁ p.2.1*χ₂ p.2.2)‖ ≤ ε) := by
  intro h
  have hh := h χ ((χ^2)⁻¹) χ
  rw [linear_discrepancy_one χ hχ] at hh
  exact (not_le_of_gt hε) hh

#print axioms not_linear_discrepancy_small
end Erdos3LinearQuadraticDiscrepancyBarrier
