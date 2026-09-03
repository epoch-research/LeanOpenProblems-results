import Submission.GaussianSmoothedPolynomialCounts
import Submission.GaussianPrimePatternSieve

/-! A smoothed Lambda-squared Gaussian sieve. Unlike the earlier sharp-box
bound, its termwise error does not carry an unavoidable factor R. All root
counts and all sieve weights remain explicit. No optimization sufficient to
exclude a prime ray is asserted. -/
namespace Erdos952Investigation.GaussianSmoothedSieve
open GaussianIdealBoxCounts GaussianPolynomialBoxCounts GaussianWeightedSieve
open GaussianPrimePatternSieve GaussianSmoothedPolynomialCounts
open scoped BigOperators Classical
set_option maxHeartbeats 0
noncomputable section
local instance : GCDMonoid GaussianInt := EuclideanDomain.gcdMonoid GaussianInt
local instance (a : GaussianInt) (R : ℕ) : Fintype (Box a R) := Fintype.ofFinite _

lemma finite_sample_sieve {Ω : Type*} [Fintype Ω] (t : Ω → GaussianInt)
    (D : Finset GaussianInt) (hD : 1 ∈ D) (w : GaussianInt → ℝ) (hw : w 1 = 1)
    (P : Polynomial GaussianInt) :
    (∑ s, if Sifted D P (t s) then (1 : ℝ) else 0) ≤
      ∑ d ∈ D, ∑ e ∈ D, w d*w e*(∑ s, if lcm d e ∣ P.eval (t s) then 1 else 0) := by
  have hpoint (d e z : GaussianInt) :
      (if d ∣ P.eval z then w d else 0)*(if e ∣ P.eval z then w e else 0) =
      w d*w e*(if lcm d e ∣ P.eval z then 1 else 0) := by
    by_cases hd : d ∣ P.eval z <;> by_cases he : e ∣ P.eval z <;> simp [hd,he,lcm_dvd_iff]
  calc
    _ ≤ ∑ s, (∑ d ∈ D, if d ∣ P.eval (t s) then w d else 0)^2 := by
      apply Finset.sum_le_sum
      intro s _
      by_cases hs : Sifted D P (t s)
      · rw [if_pos hs,weights_eq_one D hD w hw P (t s) hs]
        norm_num
      · rw [if_neg hs]
        exact sq_nonneg _
    _ = ∑ s, ∑ d ∈ D, ∑ e ∈ D,
        w d*w e*(if lcm d e ∣ P.eval (t s) then 1 else 0) := by
      simp_rw [pow_two,Finset.sum_mul_sum,hpoint]
    _ = ∑ d ∈ D, ∑ e ∈ D, ∑ s,
        w d*w e*(if lcm d e ∣ P.eval (t s) then 1 else 0) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.sum_comm]
    _ = _ := by simp_rw [← Finset.mul_sum]

lemma smoothed_lambda_sq (D : Finset GaussianInt) (hD : 1 ∈ D)
    (w : GaussianInt → ℝ) (hw : w 1 = 1) (P : Polynomial GaussianInt)
    (a b : GaussianInt) (R : ℕ) :
    smoothedCount (Sifted D P) a b R ≤
      ∑ d ∈ D, ∑ e ∈ D, w d*w e*smoothedEvalCount (lcm d e) P a b R := by
  have hh := finite_sample_sieve (fun uv : Box a R × Box b R => uv.1.val-uv.2.val) D hD w hw P
  have hd := div_le_div_of_nonneg_right hh (sq_nonneg (R : ℝ))
  simpa only [smoothedCount_sum,smoothedEvalCount,Finset.sum_div,mul_div_assoc] using hd

def smoothedErrorSum (D : Finset GaussianInt) (w : GaussianInt → ℝ)
    (P : Polynomial GaussianInt) : ℝ :=
  ∑ d ∈ D, ∑ e ∈ D, |w d*w e| *(64*(rho P (lcm d e) : ℝ))

/-- The smoothing error is constant per root class. The level condition
on every lcm is explicit and cannot be omitted when choosing weights. -/
theorem smoothed_sifted_le_main_error (D : Finset GaussianInt)
    (hD1 : 1 ∈ D) (hD0 : ∀ d ∈ D, d ≠ 0)
    (w : GaussianInt → ℝ) (hw : w 1 = 1) (P : Polynomial GaussianInt)
    (a b : GaussianInt) (R : ℕ) (hR : 0 < R)
    (hlevel : ∀ d ∈ D, ∀ e ∈ D, (lcm d e).norm.natAbs ≤ R^2) :
    smoothedCount (Sifted D P) a b R ≤
      (R : ℝ)^2*mainSum D w P+smoothedErrorSum D w P := by
  have hp (d : GaussianInt) (hd : d ∈ D) (e : GaussianInt) (he : e ∈ D) :
      w d*w e*smoothedEvalCount (lcm d e) P a b R ≤
      (R : ℝ)^2*(w d*w e*(rho P (lcm d e) : ℝ)/((lcm d e).norm.natAbs : ℝ))+
        |w d*w e| *(64*(rho P (lcm d e) : ℝ)) := by
    have hg : lcm d e ≠ 0 := by
      rw [Ne,lcm_eq_zero_iff]
      exact not_or.mpr ⟨hD0 d hd,hD0 e he⟩
    have hh : |smoothedEvalCount (lcm d e) P a b R-
        (rho P (lcm d e) : ℝ)*(R : ℝ)^2/((lcm d e).norm.natAbs : ℝ)| ≤
        64*(rho P (lcm d e) : ℝ) := by
      simpa only [rho_of_ne_zero P _ hg] using
        smoothed_eval_error (lcm d e) hg P a b R hR (hlevel d hd e he)
    have ha := le_abs_self (w d*w e*(smoothedEvalCount (lcm d e) P a b R-
      (rho P (lcm d e) : ℝ)*(R : ℝ)^2/((lcm d e).norm.natAbs : ℝ)))
    rw [abs_mul] at ha
    have h := ha.trans (mul_le_mul_of_nonneg_left hh (abs_nonneg (w d*w e)))
    calc
      _ = (R : ℝ)^2*(w d*w e*(rho P (lcm d e) : ℝ)/((lcm d e).norm.natAbs : ℝ))+
          w d*w e*(smoothedEvalCount (lcm d e) P a b R-
            (rho P (lcm d e) : ℝ)*(R : ℝ)^2/((lcm d e).norm.natAbs : ℝ)) := by ring
      _ ≤ _ := add_le_add le_rfl h
  apply (smoothed_lambda_sq D hD1 w hw P a b R).trans
  calc
    _ ≤ ∑ d ∈ D, ∑ e ∈ D,
        ((R : ℝ)^2*(w d*w e*(rho P (lcm d e) : ℝ)/((lcm d e).norm.natAbs : ℝ))+
          |w d*w e| *(64*(rho P (lcm d e) : ℝ))) :=
      Finset.sum_le_sum (fun d hd => Finset.sum_le_sum (fun e he => hp d hd e he))
    _ = _ := by simp only [mainSum,smoothedErrorSum,Finset.sum_add_distrib,Finset.mul_sum]

/-- Every genuine prime translate is included. Its small-prime exceptions
have total smoothed weight at most 4*k*|Q|. -/
theorem smoothed_prime_le_main_error {ι : Type*} [Fintype ι]
    (z : ι → GaussianInt) (D Q : Finset GaussianInt) (hD : Supported D Q)
    (hD1 : 1 ∈ D) (hD0 : ∀ d ∈ D, d ≠ 0)
    (w : GaussianInt → ℝ) (hw : w 1 = 1) (a b : GaussianInt) (R : ℕ) (hR : 0 < R)
    (hlevel : ∀ d ∈ D, ∀ e ∈ D, (lcm d e).norm.natAbs ≤ R^2) :
    smoothedCount (fun t => ∀ i, Prime (t+z i)) a b R ≤
      (R : ℝ)^2*mainSum D w (patternPolynomial z)+smoothedErrorSum D w (patternPolynomial z)+
        4*(Fintype.card ι : ℝ)*(Q.card : ℝ) := by
  have hp := smoothed_count_le_add (fun t => ∀ i, Prime (t+z i))
    (Sifted D (patternPolynomial z)) (fun t => t ∈ exceptionSet z Q) a b R
    (prime_pattern_sifted_or_exception z D Q hD)
  have hs := smoothed_sifted_le_main_error D hD1 hD0 w hw (patternPolynomial z)
    a b R hR hlevel
  have he := smoothed_finset_le (exceptionSet z Q) a b R hR
  have hc : ((exceptionSet z Q).card : ℝ) ≤ 4*(Fintype.card ι : ℝ)*(Q.card : ℝ) := by
    exact_mod_cast exceptionSet_card_le z Q
  linarith

#print axioms smoothed_lambda_sq
#print axioms smoothed_sifted_le_main_error
#print axioms smoothed_prime_le_main_error
end
end Erdos952Investigation.GaussianSmoothedSieve
