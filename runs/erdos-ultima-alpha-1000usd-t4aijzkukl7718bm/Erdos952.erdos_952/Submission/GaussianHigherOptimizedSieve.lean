import Submission.GaussianHigherPolynomialCounts
import Submission.GaussianSelbergMainOptimization

/-! Higher-order Gaussian sieve with optimal main term and a fully explicit
polynomial-prefactor geometric error. This does not estimate the denominator
uniformly over growing prime paths. -/
namespace Erdos952Investigation.GaussianHigherOptimizedSieve
open GaussianIdealRepresentatives GaussianIdealBoxCounts GaussianPolynomialBoxCounts GaussianWeightedSieve
open GaussianIteratedSmoothing FiniteSampleSmoothing GaussianHigherSmoothingLower
open GaussianHigherPolynomialCounts GaussianSmoothedSieve GaussianPrimePatternSieve
open GaussianSelbergMainOptimization FiniteSelbergOptimization
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 0
local instance : GCDMonoid GaussianInt := EuclideanDomain.gcdMonoid GaussianInt
local instance (a : GaussianInt) (R : ℕ) : Fintype (Box a R) := Fintype.ofFinite _

lemma norm_lcm_le (d e : GaussianInt) (hd : d ≠ 0) (he : e ≠ 0) :
    (lcm d e).norm.natAbs ≤ d.norm.natAbs*e.norm.natAbs := by
  have hp : 0 < (d*e).norm.natAbs :=
    Int.natAbs_pos.mpr (GaussianInt.norm_eq_zero.not.mpr (mul_ne_zero hd he))
  have hdiv := Int.natAbsHom.map_dvd (Zsqrtd.normMonoidHom.map_dvd (lcm_dvd_mul d e))
  simpa only [Zsqrtd.norm_mul,Int.natAbs_mul] using Nat.le_of_dvd hp hdiv

lemma higher_lambda_sq (D : Finset GaussianInt) (hD : 1 ∈ D)
    (w : GaussianInt → ℝ) (hw : w 1 = 1) (P : Polynomial GaussianInt)
    (a : GaussianInt) (R n : ℕ) :
    higherCount (Sifted D P) a R n ≤
      ∑ d ∈ D, ∑ e ∈ D, w d*w e*higherCount (fun z => lcm d e ∣ P.eval z) a R n := by
  have hh := finite_sample_sieve (kernelValue (tupleValue 0 R n) a R) D hD w hw P
  have hd := div_le_div_of_nonneg_right hh
    (show 0 ≤ (R : ℝ)^2*(Fintype.card (Sample (Box 0 R) n) : ℝ)^2 by positivity)
  simpa only [higherCount,kernelCount_sum,Finset.sum_div,mul_div_assoc] using hd

def sieveError (D : Finset GaussianInt) (R n A : ℕ) : ℝ :=
  (D.card : ℝ)^2*(A : ℝ)^2*(R : ℝ)^2*(8*(A : ℝ)/(R : ℝ))^(2*(n+2))

/-- A uniform higher-order bound. All weights are bounded by A and all
supported modulus norms are at most A; the lcm norms are then at most A^2. -/
theorem higher_sifted_bound (D : Finset GaussianInt) (hD1 : 1 ∈ D)
    (hD0 : ∀ d ∈ D, d ≠ 0) (w : GaussianInt → ℝ) (hw : w 1 = 1)
    (P : Polynomial GaussianInt) (a : GaussianInt) (R n A : ℕ)
    (hR : 0 < R) (hAR : A ≤ R) (hlevel : ∀ d ∈ D, d.norm.natAbs ≤ A)
    (hweight : ∀ d ∈ D, |w d| ≤ (A : ℝ)) :
    higherCount (Sifted D P) a R n ≤ (R : ℝ)^2*mainSum D w P+sieveError D R n A := by
  let E : ℝ := (R : ℝ)^2*(8*(A : ℝ)/(R : ℝ))^(2*(n+2))
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hpoint (d : GaussianInt) (hd : d ∈ D) (e : GaussianInt) (he : e ∈ D) :
      w d*w e*higherCount (fun z => lcm d e ∣ P.eval z) a R n ≤
        (R : ℝ)^2*(w d*w e*(rho P (lcm d e) : ℝ)/((lcm d e).norm.natAbs : ℝ))+
          (A : ℝ)^2*E := by
    have hg : lcm d e ≠ 0 := by
      simp only [ne_eq,lcm_eq_zero_iff,not_or]
      exact ⟨hD0 d hd,hD0 e he⟩
    have hm : (lcm d e).norm.natAbs ≤ A^2 := by
      apply (norm_lcm_le d e (hD0 d hd) (hD0 e he)).trans
      simpa only [pow_two] using Nat.mul_le_mul (hlevel d hd) (hlevel e he)
    have herr := higher_eval_error_uniform (lcm d e) hg P a R n A hR hAR hm
    have hwprod : |w d*w e| ≤ (A : ℝ)^2 := by
      rw [abs_mul,pow_two]
      exact mul_le_mul (hweight d hd) (hweight e he) (abs_nonneg _) (Nat.cast_nonneg _)
    have habs := le_abs_self (w d*w e*(higherCount (fun z => lcm d e ∣ P.eval z) a R n-
      (rho P (lcm d e) : ℝ)*(R : ℝ)^2/((lcm d e).norm.natAbs : ℝ)))
    rw [abs_mul] at habs
    have hh := habs.trans ((mul_le_mul_of_nonneg_left herr (abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_right hwprod hE))
    calc
      _ = (R : ℝ)^2*(w d*w e*(rho P (lcm d e) : ℝ)/((lcm d e).norm.natAbs : ℝ))+
          w d*w e*(higherCount (fun z => lcm d e ∣ P.eval z) a R n-
            (rho P (lcm d e) : ℝ)*(R : ℝ)^2/((lcm d e).norm.natAbs : ℝ)) := by ring
      _ ≤ _ := add_le_add le_rfl hh
  apply (higher_lambda_sq D hD1 w hw P a R n).trans
  calc
    _ ≤ ∑ d ∈ D, ∑ e ∈ D,
        ((R : ℝ)^2*(w d*w e*(rho P (lcm d e) : ℝ)/((lcm d e).norm.natAbs : ℝ))+
          (A : ℝ)^2*E) :=
      Finset.sum_le_sum (fun d hd => Finset.sum_le_sum (fun e he => hpoint d hd e he))
    _ = _ := by
      simp only [mainSum,sieveError,E,Finset.sum_add_distrib,Finset.mul_sum,
        Finset.sum_const,nsmul_eq_mul]
      ring

/-- Actual prime translates, retaining every small-prime exception. -/
theorem higher_prime_bound {κ : Type*} [Fintype κ] (z : κ → GaussianInt)
    (D Q : Finset GaussianInt) (hD : Supported D Q) (hD1 : 1 ∈ D)
    (hD0 : ∀ d ∈ D, d ≠ 0) (w : GaussianInt → ℝ) (hw : w 1 = 1)
    (a : GaussianInt) (R n A : ℕ) (hR : 0 < R) (hAR : A ≤ R)
    (hlevel : ∀ d ∈ D, d.norm.natAbs ≤ A) (hweight : ∀ d ∈ D, |w d| ≤ (A : ℝ)) :
    higherCount (fun t => ∀ i, Prime (t+z i)) a R n ≤
      (R : ℝ)^2*mainSum D w (patternPolynomial z)+sieveError D R n A+
        4*(Fintype.card κ : ℝ)*(Q.card : ℝ) := by
  letI : Nonempty (Box 0 R) := box_nonempty 0 R hR
  have hp := kernelCount_le_add (tupleValue 0 R n) (fun t => ∀ i, Prime (t+z i))
    (Sifted D (patternPolynomial z)) (fun t => t ∈ exceptionSet z Q)
    (prime_pattern_sifted_or_exception z D Q hD) a R
  have hs := higher_sifted_bound D hD1 hD0 w hw (patternPolynomial z) a R n A hR hAR hlevel hweight
  have he := kernelCount_finset_le (tupleValue 0 R n) (exceptionSet z Q) a R hR
  have hc : ((exceptionSet z Q).card : ℝ) ≤ 4*(Fintype.card κ : ℝ)*(Q.card : ℝ) := by
    exact_mod_cast exceptionSet_card_le z Q
  change higherCount (fun t => ∀ i, Prime (t+z i)) a R n ≤
    higherCount (Sifted D (patternPolynomial z)) a R n+_ at hp
  linarith

/-- Exact optimal main term with the same fully explicit error. The
hypotheses on local root densities have not been estimated away. -/
theorem optimized_higher_sifted_bound {ι : Type*} (D : Finset (Finset ι))
    (hD : DownClosed D) (hD0 : ∅ ∈ D) (g : ι → GaussianInt) (hg : ∀ i, Prime (g i))
    (hc : Pairwise (fun i j => IsCoprime (g i) (g j))) (P : Polynomial GaussianInt)
    (hρ : ∀ i, 0 < rho P (g i) ∧ rho P (g i) < (g i).norm.natAbs)
    (a : GaussianInt) (R n A : ℕ) (hR : 0 < R) (hAR : A ≤ R)
    (hlevel : ∀ s ∈ D, (modulus g s).norm.natAbs ≤ A) :
    higherCount (Sifted (modulusSupport D g) P) a R n ≤
      (R : ℝ)^2/denominator D (fun i => localDensity P (g i))+
        sieveError (modulusSupport D g) R n A := by
  obtain ⟨w,hw,hm,hweight⟩ := exists_gaussian_sieve_weights D hD hD0 g hg hc P hρ
  have h1 : 1 ∈ modulusSupport D g := Finset.mem_image.mpr ⟨∅,hD0,by simp [modulus]⟩
  have h0 (d : GaussianInt) (hd : d ∈ modulusSupport D g) : d ≠ 0 := by
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hd
    exact modulus_ne_zero g (fun i => (hg i).ne_zero) s
  have hl (d : GaussianInt) (hd : d ∈ modulusSupport D g) : d.norm.natAbs ≤ A := by
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hd
    exact hlevel s hs
  have hw' (d : GaussianInt) (hd : d ∈ modulusSupport D g) : |w d| ≤ (A : ℝ) :=
    (hweight d hd).trans (by exact_mod_cast hl d hd)
  have hh := higher_sifted_bound _ h1 h0 w hw P a R n A hR hAR hl hw'
  simpa only [hm,mul_one_div] using hh

#print axioms higher_sifted_bound
#print axioms higher_prime_bound
#print axioms optimized_higher_sifted_bound
end
end Erdos952Investigation.GaussianHigherOptimizedSieve
