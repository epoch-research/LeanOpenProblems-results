import Submission.SelbergQuadraticEnergy

/-! Coefficient cost for the quadratic logarithmic Selberg profile. -/
namespace Erdos970.FiniteSelberg
open Finset Real
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma prime_quadratic_support (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (R : ℕ) (hR : 0 < R) (Q : Finset ι) (hQ : Q ∉ divisorSupport p R) :
    primeQuadraticProfile p (log R) Q = 0 := by
  have hRQ : R < ∏ i ∈ Q, p i := by simpa only [mem_divisorSupport, not_le] using hQ
  apply quadraticProfile_zero _ _ (log_natCast_nonneg R)
  rw [primeLogLocation_eq_log_prod p hp]
  apply log_le_log (by exact_mod_cast hR)
  exact_mod_cast hRQ.le

lemma prime_quadratic_cost_le (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (R : ℕ) (hR : 0 < R) :
    kernelCost (fun i => 1 / (p i : ℝ))
      (fun Q => weight (fun i => 1 / (p i : ℝ)) Q * primeQuadraticProfile p (log R) Q) ≤
        log (R : ℝ) ^ 2 * exp 2 * R := by
  let f := primeQuadraticProfile p (log R)
  let D := divisorSupport p R
  have hf (Q : Finset ι) : 0 ≤ f Q := le_max_right _ _
  have hpred (i : ι) : 0 < (p i : ℝ) - 1 := by
    have hh : (1 : ℝ) < p i := by exact_mod_cast (hp i).one_lt
    linarith
  have hfactor (i : ι) : (1 + 1 / (p i : ℝ)) / (1 - 1 / (p i : ℝ)) =
      ((p i : ℝ) + 1) / (p i - 1) := by
    have hpi : (p i : ℝ) ≠ 0 := by exact_mod_cast (hp i).ne_zero
    field_simp [hpi, (hpred i).ne']
    <;> ring
  rw [kernelCost_weighted _ (prime_marginals p hp) _ hf]
  simp_rw [hfactor]
  calc
    _ = ∑ Q ∈ D, f Q * ∏ i ∈ Q, ((p i : ℝ) + 1) / (p i - 1) := by
      symm
      apply sum_subset (subset_univ _)
      intro Q hQ hQD
      rw [show f Q = 0 from prime_quadratic_support p hp R hR Q hQD, zero_mul]
    _ ≤ log (R : ℝ) ^ 2 * ∑ Q ∈ D, ∏ i ∈ Q, ((p i : ℝ) + 1) / (p i - 1) := by
      rw [mul_sum]
      apply sum_le_sum
      intro Q hQ
      have hfle : f Q ≤ log (R : ℝ) ^ 2 :=
        max_le (sub_le_self _ (sq_nonneg _)) (sq_nonneg _)
      apply mul_le_mul_of_nonneg_right hfle
      apply prod_nonneg
      intro i hi
      exact div_nonneg (by positivity) (hpred i).le
    _ ≤ log (R : ℝ) ^ 2 * (exp 2 * R) := mul_le_mul_of_nonneg_left
      (divisor_cost_sum_le p hp hinj R) (sq_nonneg _)
    _ = _ := by ring

#print axioms prime_quadratic_cost_le
end Erdos970.FiniteSelberg
