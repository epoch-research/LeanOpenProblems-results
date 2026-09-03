import Submission.FloorDiagonalCount
import Submission.MellinDivisorCoefficient
import Submission.TypeIPolynomial

/-! An explicit absolute bound for the equal-Mangoldt-factor diagonal.
The off-diagonal signed four-factor sum is not estimated here. -/
namespace Erdos972VaughanDiagonalBound

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta
open Erdos972FloorDiagonalCount Erdos972MellinDivisorCoefficient
open Erdos972TypeIPolynomial Erdos972Vaughan Erdos972DivisorCovariance

lemma divisorCoeff_abs_le (U n : ℕ) : |divisorCoeff U n| ≤ (U : ℝ) + 1 := by
  by_cases hn : n = 0
  · subst n
    simp only [divisorCoeff, ArithmeticFunction.map_zero, abs_zero]
    positivity
  have hn0 : 0 < n := Nat.pos_of_ne_zero hn
  rw [divisorCoeff_eq]
  apply (abs_sub _ _).trans
  have h1 : |(1 : ArithmeticFunction ℝ) n| ≤ 1 := by
    rw [ArithmeticFunction.one_apply]
    split_ifs <;> norm_num
  have hc : (cutoff (μ : ArithmeticFunction ℝ) U * ζ) n =
      divisorPolynomial U (slopeCoeff U) n := by
    rw [ArithmeticFunction.coe_mul_zeta_apply]
    exact supported_divisor_sum U n (slopeCoeff U) hn0
      (fun d hd => slopeCoeff_support le_rfl hd)
  rw [hc]
  have hb := (divisorPolynomial_abs_le U n (slopeCoeff U)).trans (slopeCoeff_mass U U)
  linarith only [h1, hb]

/-- The equal-factor contribution, indexed by the common Mangoldt factor.
For p>V the tail Mangoldt value is Lambda(p); the row condition encodes
floor(alpha*m*p) = p*floor(alpha*m) exactly. -/
noncomputable def vaughanDiagonal (α : ℝ) (N U V : ℕ) : ℝ :=
  ∑ p ∈ Ioc V N, ∑ m ∈ diagonalRows α N p,
    divisorCoeff U m * divisorCoeff U ⌊α * m⌋₊ * (vonMangoldt p)^2

/-- This estimate is absolute, so it makes no claim about the signs of the
individual diagonal terms. -/
theorem vaughan_diagonal_bound {α : ℝ} {a q N U V : ℕ}
    (hα : 0 ≤ α) (hq : 0 < q) (haq : a.Coprime q)
    (happrox : |α - (a : ℝ) / q| * N ≤ 1)
    (hN : N ≤ q ^ 2) (hV : 0 < V) :
    |vaughanDiagonal α N U V| ≤
      ((U : ℝ) + 1)^2 * (Real.log N)^2 *
        (10 * N / (V : ℝ) + (2 * N / (q : ℝ) + 5 * q) *
          (1 + Real.log (2 * q : ℕ)) + 2 * q) := by
  apply weighted_diagonal_bound hα hq haq happrox hN hV _ (by positivity)
  intro p hp m _hm
  have hp0 : 0 < p := hV.trans (mem_Ioc.mp hp).1
  have hpN : p ≤ N := (mem_Ioc.mp hp).2
  have hL : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hΛ : vonMangoldt p ≤ Real.log N :=
    vonMangoldt_le_log.trans (Real.log_le_log (Nat.cast_pos.mpr hp0) (Nat.cast_le.mpr hpN))
  have hsq : (vonMangoldt p)^2 ≤ (Real.log N)^2 :=
    pow_le_pow_left₀ vonMangoldt_nonneg hΛ 2
  simp only [abs_mul, abs_pow, sq_abs]
  have hh := mul_le_mul (divisorCoeff_abs_le U m) (divisorCoeff_abs_le U ⌊α * m⌋₊)
    (abs_nonneg _) (by positivity)
  have hh' := mul_le_mul hh hsq (sq_nonneg _) (by positivity)
  simpa only [pow_two] using hh'

#print axioms divisorCoeff_abs_le
#print axioms vaughan_diagonal_bound

end Erdos972VaughanDiagonalBound
