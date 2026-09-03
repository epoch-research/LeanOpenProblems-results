import Submission.PrimeGcdRows
import Submission.TypeISmallBounds

/-! An actual signed one-prime covariance bound for the positive Vaughan
remainder. The finite gcd-pattern modulus and its inversion cost are explicit. -/
namespace Erdos972PositiveRemainderPrimeCovariance

open Finset ArithmeticFunction
open Erdos972PrimePowerError Erdos972ChebyshevRowMean Erdos972WeightedBeattyRows
open Erdos972PrimeGcdRows Erdos972GcdProfileExpansion Erdos972GcdProfileCovariance
open Erdos972RemainderGcdProfile Erdos972RemainderPositiveTypeI
open Erdos972Vaughan Erdos972DoubleVaughan Erdos972TypeIPolynomial
open Erdos972DivisorCovariance Erdos972LogarithmicCovariance
open Erdos972CovariancePerturbation Erdos972TypeISmallBounds Erdos972LipschitzLogWeights

noncomputable def positiveRemainder (U V n : ℕ) : ℝ := max (typeIIPart U V n) 0

lemma positive_profile_height (U V r N : ℕ) :
    |positiveRemainderProfile U V r (Real.log N)| ≤
      (U*V:ℕ)*(Real.log N+2*Real.log (U*V:ℕ)) := by
  have ha := (divisorPolynomial_abs_le (U*V) r (slopeCoeff U)).trans (slopeCoeff_mass U (U*V))
  have hb := (divisorPolynomial_abs_le (U*V) r (constantCoeff U V)).trans (constantCoeff_mass U V (U*V))
  have hp : |max (-affineProfile U V r (Real.log N)) 0| ≤ |affineProfile U V r (Real.log N)| := by
    rw [abs_of_nonneg (le_max_right _ _)]
    apply max_le
    · exact neg_le_abs _
    · exact abs_nonneg _
  apply hp.trans
  unfold affineProfile
  apply (abs_add_le _ _).trans
  rw [abs_mul, abs_of_nonneg (Real.log_natCast_nonneg N)]
  have hh := mul_le_mul_of_nonneg_left ha (Real.log_natCast_nonneg N)
  nlinarith only [hh, hb]

lemma positive_remainder_profile_error {U V n : ℕ} (hU : 1 ≤ U) (hV : 0 < V)
    (hn : 0 < n) :
    |positiveRemainder U V n-gcdWeight (U*V).factorial (positiveRemainderProfile U V) n| ≤
      cutoff Λ V n := by
  have he : typeIPart U V n =
      affineProfile U V (n.gcd (U*V).factorial) (Real.log n)+cutoff Λ V n := by
    rw [typeIPart_polynomial U V hV hn]
    simp only [affineProfile, divisorPolynomial_gcd_factorial]
  rw [positiveRemainder, positive_remainder_eq_negative_typeI hU, gcdWeight, positiveRemainderProfile]
  have hh := abs_max_zero_sub_max_zero_le (-typeIPart U V n)
    (-affineProfile U V (n.gcd (U*V).factorial) (Real.log n))
  apply hh.trans_eq
  rw [he]
  have hid : -(affineProfile U V (n.gcd (U*V).factorial) (Real.log n)+cutoff Λ V n)-
      -affineProfile U V (n.gcd (U*V).factorial) (Real.log n) = -cutoff Λ V n := by ring
  rw [hid, abs_neg, abs_of_nonneg (cutoff_vonMangoldt_nonneg V n)]

lemma positive_remainder_profile_l1 {U V : ℕ} (hU : 1 ≤ U) (hV : 0 < V) (N : ℕ) :
    total N (fun n => |positiveRemainder U V n-
      gcdWeight (U*V).factorial (positiveRemainderProfile U V) n|) ≤ 7*(V:ℝ) := by
  apply (sum_le_sum (fun n hn => positive_remainder_profile_error hU hV (mem_Ioc.mp hn).1)).trans
  exact (cutoff_mangoldt_sum_le V N).trans (psi_le_seven_mul (Nat.cast_nonneg V))

/-- This bound applies to the actual positive remainder, not just its
finite-profile approximation. The small-input error is retained. -/
theorem positive_remainder_prime_covariance_precise {α E : ℝ} (hα : 1 < α) (hI : Irrational α)
    (hE : 0 ≤ E) {U V N : ℕ} (hU : 1 ≤ U) (hV : 0 < V) (hN : 0 < N)
    (hrows : ∀ d ∈ (U*V).factorial.divisors, ∀ Q ≤ floorMul (α*d) (N/d),
      |outputRow (α*d) (fun q => Λ q) Q-(1/(α*d))*Chebyshev.psi Q| ≤ E) :
    |covariance N (positiveRemainder U V) (fun n => Λ (floorMul α n))| ≤
      (U*V:ℕ)*centeredMeanBudget (rowMean α) 1 N+
      (2*(U*V:ℕ)*(Real.log N+Real.log (U*V:ℕ)))*
        (profileCost (U*V).factorial*(E+2*Real.log (α*N)+7)+E+2*Real.log (α*N))+
      14*(V:ℝ)*Real.log (α*N) := by
  have hh := prime_gcd_covariance_bound hα hI hE (Nat.factorial_pos _).ne' hN
    (positiveRemainderProfile U V) (L := (U*V:ℕ)) (Nat.cast_nonneg _)
    (fun r _ => positiveRemainderProfile_lipschitz U V r)
    (fun r _ => positive_profile_height U V r N) hrows
  have hpert := covariance_second_perturb hN (fun n => Λ (floorMul α n))
    (positiveRemainder U V) (gcdWeight (U*V).factorial (positiveRemainderProfile U V))
    (A := Real.log (α*N)) (by
      intro n hn
      rw [abs_of_nonneg vonMangoldt_nonneg]
      exact vonMangoldt_le_log.trans (log_floorMul_le hα.le hn))
  rw [covariance_comm N (fun n => Λ (floorMul α n)) (positiveRemainder U V),
    covariance_comm N (fun n => Λ (floorMul α n)) (gcdWeight (U*V).factorial (positiveRemainderProfile U V))] at hpert
  have hlog : 0 ≤ Real.log (α*N) := Real.log_nonneg
    (one_le_mul_of_one_le_of_one_le hα.le (by exact_mod_cast hN))
  have hl1 := mul_le_mul_of_nonneg_left (positive_remainder_profile_l1 hU hV N)
    (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hlog)
  have ht := abs_sub_le (covariance N (positiveRemainder U V) (fun n => Λ (floorMul α n)))
    (covariance N (gcdWeight (U*V).factorial (positiveRemainderProfile U V)) (fun n => Λ (floorMul α n))) 0
  simp only [sub_zero] at ht
  nlinarith only [ht, hh, hpert, hl1]

/-- A coarser polynomial-logarithmic budget convenient for taking good-scale
limits with fixed cutoffs. It does not hide the factorial modulus requirement. -/
theorem positive_remainder_prime_covariance_bound {α E : ℝ} (hα : 1 < α) (hI : Irrational α)
    (hE : 0 ≤ E) {U V N : ℕ} (hU : 1 ≤ U) (hV : 0 < V) (hDN : U*V ≤ N)
    (hrows : ∀ d ∈ (U*V).factorial.divisors, ∀ Q ≤ floorMul (α*d) (N/d),
      |outputRow (α*d) (fun q => Λ q) Q-(1/(α*d))*Chebyshev.psi Q| ≤ E) :
    |covariance N (positiveRemainder U V) (fun n => Λ (floorMul α n))| ≤
      (U*V:ℕ)*centeredMeanBudget (rowMean α) 1 N+
      100*(U*V:ℕ)*(profileCost (U*V).factorial+1)*(1+Real.log (α*N))^2*(E+1) := by
  have hD : 0 < U*V := Nat.mul_pos hU hV
  have hN : 0 < N := hD.trans_le hDN
  have hα0 : 0 < α := by linarith
  let D : ℝ := (U*V:ℕ)
  let C : ℝ := profileCost (U*V).factorial
  let l : ℝ := Real.log (α*N)
  let L : ℝ := 1+l
  have hD0 : 0 ≤ D := Nat.cast_nonneg _
  have hC0 : 0 ≤ C := profileCost_nonneg _
  have hl : 0 ≤ l := Real.log_nonneg (one_le_mul_of_one_le_of_one_le hα.le (by exact_mod_cast hN))
  have hL : 1 ≤ L := by dsimp [L]; linarith only [hl]
  have hlogN : Real.log N ≤ l := Real.log_le_log (Nat.cast_pos.mpr hN)
    (le_mul_of_one_le_left (Nat.cast_nonneg N) hα.le)
  have hlogD : Real.log (U*V:ℕ) ≤ l := (Erdos972ExponentialSum.monotone_log_natCast hDN).trans hlogN
  have hVle : (V:ℝ) ≤ D := by dsimp only [D]; exact_mod_cast (show V ≤ U*V by nlinarith only [hU])
  have hK : 2*D*(Real.log N+Real.log (U*V:ℕ)) ≤ 4*D*L := by
    have hh := mul_le_mul_of_nonneg_left (add_le_add hlogN hlogD) (by positivity : 0 ≤ 2*D)
    dsimp only [L]
    nlinarith only [hh, hD0]
  have hbr : C*(E+2*l+7)+E+2*l ≤ 10*(C+1)*L*(E+1) := by
    have hsmall : E+2*l+7 ≤ 10*L*(E+1) := by
      dsimp only [L]
      nlinarith only [hE, hl, mul_nonneg hE hl]
    have hh := mul_le_mul_of_nonneg_left hsmall (by linarith : 0 ≤ C+1)
    nlinarith only [hh]
  have hprod := mul_le_mul hK hbr (by positivity : 0 ≤ C*(E+2*l+7)+E+2*l)
    (by positivity : 0 ≤ 4*D*L)
  have hrest : 14*(V:ℝ)*l ≤ 14*D*(C+1)*L^2*(E+1) := by
    have hlL : l ≤ L^2 := by dsimp [L]; nlinarith only [hl, sq_nonneg l]
    have hbig : L^2 ≤ (C+1)*L^2*(E+1) := by
      have hh := le_mul_of_one_le_left (sq_nonneg L) (by linarith : 1 ≤ C+1)
      exact hh.trans (le_mul_of_one_le_right (by positivity) (by linarith : 1 ≤ E+1))
    have hh := mul_le_mul hVle (hlL.trans hbig) hl hD0
    nlinarith only [hh]
  have hp := positive_remainder_prime_covariance_precise hα hI hE hU hV hN hrows
  change _ ≤ D*centeredMeanBudget (rowMean α) 1 N+
    2*D*(Real.log N+Real.log (U*V:ℕ))*(C*(E+2*l+7)+E+2*l)+14*(V:ℝ)*l at hp
  change _ ≤ D*centeredMeanBudget (rowMean α) 1 N+100*D*(C+1)*L^2*(E+1)
  have hpos : 0 ≤ D*(C+1)*L^2*(E+1) := by positivity
  nlinarith only [hp, hprod, hrest, hpos]

#print axioms positive_remainder_prime_covariance_precise
#print axioms positive_remainder_prime_covariance_bound

end Erdos972PositiveRemainderPrimeCovariance
