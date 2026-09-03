import FormalConjecturesUtil

/-!
Exact structural checks for quadratic factorizations of binary quartic sections.
These do not estimate the unrestricted representation count.
-/
namespace Erdos322Research.QuarticQuadraticFactorRecheck

/-- The familiar Pythagorean locus produces two quadratic factors, not
necessarily a repeated quadratic factor or an additive-triple family. -/
theorem pythagorean_section_factorization (h c b x y : ℚ)
    (hp : b^2 = h^2 + c^2) :
    x^4 + (b*y-x)^4 + (h*y)^4 + (c*y)^4 =
      2 * (x^2-b*x*y+(b^2-h*c)*y^2) *
        (x^2-b*x*y+(b^2+h*c)*y^2) := by
  have hp2 : b^4 = (h^2+c^2)^2 := by
    calc
      b^4 = (b^2)^2 := by ring
      _ = (h^2+c^2)^2 := by rw [hp]
  linear_combination -y^4 * hp2

/-- A nonadditive example coming from the Pythagorean triple `(3,4,5)`. -/
theorem section_345 (x y : ℚ) :
    x^4 + (5*y-x)^4 + (3*y)^4 + (4*y)^4 =
      2 * (x^2-5*x*y+13*y^2) * (x^2-5*x*y+37*y^2) := by
  ring

/-- Both displayed quadratic factors are positive definite. -/
theorem factors_positive (x y : ℚ) (hne : x ≠ 0 ∨ y ≠ 0) :
    0 < x^2-5*x*y+13*y^2 ∧ 0 < x^2-5*x*y+37*y^2 := by
  have hs := sq_nonneg (2*x-5*y)
  have hy := sq_nonneg y
  have hpos : 0 < (2*x-5*y)^2 + 27*y^2 := by
    rcases hne with hx | hy0
    · by_cases hy0 : y = 0
      · subst y
        simpa using sq_pos_of_ne_zero (mul_ne_zero (by norm_num : (2:ℚ) ≠ 0) hx)
      · have hp := sq_pos_of_ne_zero hy0
        nlinarith
    · have hp := sq_pos_of_ne_zero hy0
      nlinarith
  constructor <;> nlinarith

private def witness : Fin 4 → ℕ := ![2, 3, 3, 4]

/-- The section has a strictly positive, primitive, nonadditive integer tuple.
Thus quadratic factorization alone does not put a tuple in the additive locus. -/
theorem positive_nonadditive_witness :
    (∀ i, 0 < witness i) ∧
    Finset.univ.gcd witness = 1 ∧
    (∀ i j l : Fin 4, i ≠ j → i ≠ l → j ≠ l →
      witness i + witness j ≠ witness l) ∧
    (witness 0 + witness 1)^2 = witness 2^2 + witness 3^2 ∧
    (∑ i, witness i^4) = 434 := by
  decide

end Erdos322Research.QuarticQuadraticFactorRecheck
