import Submission.QuarticRationalSpecialization
import Submission.QuarticSquareMultiplier

/-! The square-multiplier obstruction applies to arbitrary rational polynomial
formulas, including formulas whose denominator vanishes at the test inputs. -/
namespace Erdos322Research.QuarticRationalSquareMultiplier

open QuarticSquareMultiplier

/-- A generic rational squaring identity would have to specialize to a valid
representation at every represented natural input target. -/
theorem rational_formula_gives_multiplier
    (C : ℕ) (P : Fin 4 → MvPolynomial (Fin 4) ℚ) (D : MvPolynomial (Fin 4) ℚ)
    (hD : D ≠ 0)
    (h : ∑ i, P i^4 = D^4*(MvPolynomial.C (C : ℚ)*(∑ i : Fin 4, MvPolynomial.X i^4)^2)) :
    UniversalSquareMultiplier C := by
  rintro n ⟨a,ha⟩
  obtain ⟨b,hb⟩ := QuarticRationalSpecialization.multivariate_specialization P D
    (MvPolynomial.C (C : ℚ)*(∑ i : Fin 4, MvPolynomial.X i^4)^2) hD h a
  refine ⟨b,?_⟩
  simpa only [map_mul,map_pow,map_sum,MvPolynomial.eval_C,MvPolynomial.eval_X,
    ha,Nat.cast_mul,Nat.cast_pow] using hb

/-- Necessary two-adic shape for any such generic rational formula. This is
not an assertion that a formula exists for the surviving multipliers. -/
theorem rational_formula_multiplier_shape
    (C : ℕ) (hC : 0 < C) (P : Fin 4 → MvPolynomial (Fin 4) ℚ)
    (D : MvPolynomial (Fin 4) ℚ) (hD : D ≠ 0)
    (h : ∑ i, P i^4 = D^4*(MvPolynomial.C (C : ℚ)*(∑ i : Fin 4, MvPolynomial.X i^4)^2)) :
    ∃ m u : ℕ, C=16^m*u ∧ u%64=4 :=
  universal_multiplier_shape hC (rational_formula_gives_multiplier C P D hD h)

end Erdos322Research.QuarticRationalSquareMultiplier
