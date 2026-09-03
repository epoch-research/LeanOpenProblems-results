import Submission.ResidueDivisorCounts
import Submission.ParityFloorPrefix

/-! Centered residue-class prefixes of the actual arithmetic remainder. -/
namespace Erdos972ResidueRemainderPrefix

open Finset ArithmeticFunction Classical
open Erdos972PrimePowerError Erdos972LogarithmicCovariance
open Erdos972DivisorMeanRecenter Erdos972RecenteredRemainderPrefix
open Erdos972RecenterCovarianceBounds Erdos972TypeISmallBounds Erdos972ChebyshevRowMean
open Erdos972Vaughan Erdos972DoubleVaughan Erdos972MobiusPartialSums
open Erdos972DivisorCovariance Erdos972DivisorPairCount Erdos972LogDivisorProfiles
open Erdos972TypeIPolynomial Erdos972TypeICovariance Erdos972ParityFloorPrefix
open Erdos972ResiduePrimeRows Erdos972ResidueDivisorCounts

set_option maxHeartbeats 1500000

lemma twisted_polynomial_bound (w : ℕ → ℝ) (D X : ℕ) (a : ℕ → ℝ) {B : ℝ}
    (h : ∀ d ∈ Ioc 0 D, |∑ n ∈ (Ioc 0 X).filter (fun n => d ∣ n), w n| ≤ B) :
    |total X (fun n => divisorPolynomial D a n*w n)| ≤ B*coefficientMass D a := by
  have he : total X (fun n => divisorPolynomial D a n*w n) =
      ∑ d ∈ Ioc 0 D, a d*(∑ n ∈ (Ioc 0 X).filter (fun n => d ∣ n), w n) := by
    simp only [total, divisorPolynomial, sum_mul, mul_sum, sum_filter]
    rw [sum_comm]
    apply sum_congr rfl
    intro d hd
    apply sum_congr rfl
    intro n hn
    split_ifs <;> simp
  rw [he]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ d ∈ Ioc 0 D, |a d| * B := by
      apply sum_le_sum
      intro d hd
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (h d hd) (abs_nonneg _)
    _ = _ := by rw [← sum_mul]; unfold coefficientMass; ring

lemma twisted_profile_bound (w : ℕ → ℝ) {D N X : ℕ} (hXN : X ≤ N)
    (a b : ℕ → ℝ) {B L : ℝ} (hB : 0 ≤ B) (hL : 1 ≤ L) (hlog : Real.log N ≤ L-1)
    (h : ∀ Y ≤ N, ∀ d ∈ Ioc 0 D,
      |∑ n ∈ (Ioc 0 Y).filter (fun n => d ∣ n), w n| ≤ B) :
    |total X (fun n => profile D a b n*w n)| ≤ 2*L*B*profileMass D a b := by
  have h1 := logPower_prefix_approx (fun n => divisorPolynomial D a n*w n) 0
    (B*coefficientMass D a) X 1 (by
      intro Y hY
      simpa only [zero_mul, sub_zero] using twisted_polynomial_bound w D Y a (h Y (hY.trans hXN)))
  simp only [pow_one, zero_mul, sub_zero] at h1
  have h0 := twisted_polynomial_bound w D X b (h X hXN)
  have he : total X (fun n => profile D a b n*w n) =
      total X (fun n => Real.log n*(divisorPolynomial D a n*w n))+
        total X (fun n => divisorPolynomial D b n*w n) := by
    simp only [total, profile, add_mul, mul_assoc, sum_add_distrib]
  rw [he]
  apply (abs_add_le _ _).trans
  have hx : Real.log X ≤ L-1 := (Erdos972ExponentialSum.monotone_log_natCast hXN).trans hlog
  have hm := mul_le_mul_of_nonneg_right hx
    (mul_nonneg hB (coefficientMass_nonneg D a))
  have ha : 0 ≤ B*coefficientMass D a := mul_nonneg hB (coefficientMass_nonneg D a)
  have hb : 0 ≤ B*coefficientMass D b := mul_nonneg hB (coefficientMass_nonneg D b)
  have hbL := mul_le_mul_of_nonneg_right hL hb
  unfold profileMass
  change |total X (fun n => Real.log n*(divisorPolynomial D a n*w n))| ≤ _ at h1
  nlinarith only [h1, h0, hm, ha, hb, hbL]

/-- A generic twisted-prefix estimate, retaining the empirical input mean. -/
theorem centered_twisted_prefix_bound (w : ℕ → ℝ) {W v N X : ℕ}
    (hW : 0 < W) (hWv : W*W ≤ v) (hvN : v ≤ N) (hXN : X ≤ N)
    {L Ep B : ℝ} (hL : 1 ≤ L) (hlog : Real.log N ≤ L-1)
    (hm : |reciprocalMoebius W| ≤ 1) (hB : 0 ≤ B)
    (hw : ∀ n, |w n| ≤ 1)
    (hprime : |total X (fun n => vonMangoldt n*w n)| ≤ Ep)
    (hdiv : ∀ Y ≤ N, ∀ d ∈ Ioc 0 v,
      |∑ n ∈ (Ioc 0 Y).filter (fun n => d ∣ n), w n| ≤ B) :
    |total X (fun n =>
      (meanCenteredTypeII W W n-total N (fun n => meanCenteredTypeII W W n)/N)*w n)| ≤
        Ep+20*(v : ℝ)*L^2*(B+1) := by
  have hWv' : W ≤ v := (show W ≤ W*W by nlinarith only [hW]).trans hWv
  have hv : 0 < v := hW.trans_le hWv'
  have hN : 0 < N := hv.trans_le hvN
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hL0 : 0 ≤ L := by linarith only [hL]
  let R := fun n => meanCenteredTypeII W W n
  let A := profile (W*W) (slopeCoeff W) (constantCoeff W W)
  let A' := profile (1*W) (slopeCoeff 1) (constantCoeff 1 W)
  have hprofile (U V : ℕ) (hUV : U*V ≤ v) :
      |total X (fun n => profile (U*V) (slopeCoeff U) (constantCoeff U V) n*w n)| ≤
        4*(v : ℝ)*L^2*B := by
    have hh := twisted_profile_bound w hXN (slopeCoeff U) (constantCoeff U V) hB hL hlog
      (fun Y hY d hd => hdiv Y hY d
        (mem_Ioc.mpr ⟨(mem_Ioc.mp hd).1, (mem_Ioc.mp hd).2.trans hUV⟩))
    have hm' := typeI_profileMass_le hUV hL
      ((Erdos972ExponentialSum.monotone_log_natCast (hUV.trans hvN)).trans hlog)
    exact hh.trans ((mul_le_mul_of_nonneg_left hm' (show 0 ≤ 2*L*B by positivity)).trans_eq (by ring))
  have hA := hprofile W W hWv
  have hA' := hprofile 1 W (by simpa only [one_mul] using hWv')
  have hs : |total X (fun n => cutoff vonMangoldt W n*w n)| ≤ 7*(v : ℝ) := by
    apply (abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ n ∈ Ioc 0 X, cutoff vonMangoldt W n := by
        apply sum_le_sum
        intro n hn
        rw [abs_mul, abs_of_nonneg (cutoff_vonMangoldt_nonneg _ _)]
        exact (mul_le_mul_of_nonneg_left (hw n) (cutoff_vonMangoldt_nonneg _ _)).trans_eq (by ring)
      _ ≤ _ := (cutoff_mangoldt_sum_le W X).trans
        ((psi_le_seven_mul (Nat.cast_nonneg W)).trans
          (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hWv') (by norm_num)))
  have hR (n : ℕ) (hn : 0 < n) : R n = vonMangoldt n-A n+reciprocalMoebius W*A' n-cutoff vonMangoldt W n := by
    have hh := congrArg (fun f : ArithmeticFunction ℝ => f n) (mean_centered_vaughan_identity W W)
    dsimp only at hh
    rw [ArithmeticFunction.add_apply, meanCenteredTypeI_profile hW hn] at hh
    dsimp only [R, A, A']
    linarith only [hh]
  have hsum : total X (fun n => R n*w n) =
      total X (fun n => vonMangoldt n*w n)-total X (fun n => A n*w n)+
        reciprocalMoebius W*total X (fun n => A' n*w n)-
          total X (fun n => cutoff vonMangoldt W n*w n) := by
    simp only [total, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro n hn
    rw [hR n (mem_Ioc.mp hn).1]
    ring
  change |total X (fun n => A' n*w n)| ≤ 4*(v : ℝ)*L^2*B at hA'
  have hAm : |reciprocalMoebius W*total X (fun n => A' n*w n)| ≤ 4*(v : ℝ)*L^2*B := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right hm (abs_nonneg _)).trans (by simpa only [one_mul] using hA')
  have hraw : |total X (fun n => R n*w n)| ≤ Ep+8*(v : ℝ)*L^2*B+7*v := by
    rw [hsum]
    apply ((abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans
      (add_le_add (abs_sub _ _) le_rfl)) le_rfl)).trans
    linarith only [hprime, hA, hAm, hs]
  have hpoint (n : ℕ) (hn : n ∈ Ioc 0 N) : |R n| ≤ 5*(v : ℝ)*L^2 := by
    exact meanCenteredTypeII_abs_bound hW hW hWv (mem_Ioc.mp hn).1 hL
      ((Erdos972ExponentialSum.monotone_log_natCast (hWv.trans hvN)).trans hlog)
      ((Erdos972ExponentialSum.monotone_log_natCast (mem_Ioc.mp hn).2).trans hlog) hm
  have hmean : |total N R/(N : ℝ)| ≤ 5*(v : ℝ)*L^2 := by
    rw [abs_div, abs_of_pos hNR]
    apply (div_le_iff₀ hNR).mpr
    simpa only [mul_comm] using total_abs_le hpoint
  have hwX : |total X w| ≤ B := by
    simpa only [Nat.one_dvd, filter_true] using hdiv X hXN 1 (mem_Ioc.mpr ⟨by norm_num, hv⟩)
  have hcorr : |(total N R/N)*total X w| ≤ 5*(v : ℝ)*L^2*B := by
    rw [abs_mul]
    exact mul_le_mul hmean hwX (abs_nonneg _) (by positivity)
  have he : total X (fun n => (R n-total N R/N)*w n) =
      total X (fun n => R n*w n)-(total N R/N)*total X w := by
    simp only [total, sub_mul, sum_sub_distrib, mul_sum]
  change |total X (fun n => (R n-total N R/N)*w n)| ≤ _
  rw [he]
  apply (abs_sub _ _).trans
  have hvL : 7*(v : ℝ) ≤ 7*(v : ℝ)*L^2 :=
    le_mul_of_one_le_right (by positivity) (one_le_pow₀ hL)
  have hpos : 0 ≤ (v : ℝ)*L^2*B := by positivity
  have hpos' : 0 ≤ (v : ℝ)*L^2 := by positivity
  nlinarith only [hraw, hcorr, hvL, hpos, hpos']


noncomputable def centeredResidue (α : ℝ) (e j n : ℕ) : ℝ :=
  (if floorMul α n%e = j then 1 else 0)-1/(e : ℝ)

lemma centeredResidue_abs_le_one (α : ℝ) {e : ℕ} (he : 0 < e) (j n : ℕ) :
    |centeredResidue α e j n| ≤ 1 := by
  have heR : (1 : ℝ) ≤ e := by exact_mod_cast he
  have hh : 1/(e : ℝ) ≤ 1 := (div_le_one (by positivity)).mpr heR
  have h0 : 0 ≤ 1/(e : ℝ) := by positivity
  unfold centeredResidue
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith only [hh, h0]

lemma centeredResidue_prime_sum (α : ℝ) (e j X : ℕ) :
    total X (fun n => vonMangoldt n*centeredResidue α e j n) =
      inputResidueRow α e j X-Chebyshev.psi X/e := by
  simp only [total, centeredResidue, mul_sub, sum_sub_distrib, ← sum_mul,
    inputResidueRow, sum_filter, mul_ite, mul_one, mul_zero, Chebyshev.psi, Nat.floor_natCast]
  ring

lemma centeredResidue_divisor_sum (α : ℝ) (e j d X : ℕ) :
    (∑ n ∈ (Ioc 0 X).filter (fun n => d ∣ n), centeredResidue α e j n) =
      (residueDivisorPairs α X d e j).card-((X/d : ℕ) : ℝ)/e := by
  have he : ((Ioc 0 X).filter (fun n => d ∣ n)).filter (fun n => floorMul α n%e = j) =
      residueDivisorPairs α X d e j := by
    simp only [filter_filter, residueDivisorPairs]
  simp only [centeredResidue, sum_sub_distrib, ← sum_filter, sum_const, nsmul_eq_mul, he,
    mul_one, Nat.Ioc_filter_dvd_card_eq_div, mul_one_div]

lemma centeredResidue_divisor_bound (α : ℝ) {e : ℕ} (he : 0 < e) (j d X : ℕ) {B : ℝ}
    (h : |((residueDivisorPairs α X d e j).card : ℝ)-(X : ℝ)/(d*e)| ≤ B) :
    |∑ n ∈ (Ioc 0 X).filter (fun n => d ∣ n), centeredResidue α e j n| ≤ B+1 := by
  have heR : (1 : ℝ) ≤ e := by exact_mod_cast he
  have he0 : (0 : ℝ) < e := by positivity
  have hfl : |(X : ℝ)/d-(X/d : ℕ)| ≤ 1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr Nat.cast_div_le)]
    have hh := Nat.lt_floor_add_one ((X : ℝ)/d)
    rw [Nat.floor_div_eq_div] at hh
    linarith only [hh]
  have hoff : |(X : ℝ)/(d*e)-((X/d : ℕ) : ℝ)/e| ≤ 1 := by
    rw [div_mul_eq_div_div, ← sub_div, abs_div, abs_of_pos he0]
    exact (div_le_div_of_nonneg_right hfl he0.le).trans ((div_le_one he0).mpr heR)
  rw [centeredResidue_divisor_sum]
  exact (abs_sub_le _ ((X : ℝ)/(d*e)) _).trans (add_le_add h hoff)

/-- Each residue is centered by its exact density 1/e before the globally
centered actual arithmetic remainder is summed. -/
theorem centered_residue_remainder_prefix (α : ℝ) {W v N X e : ℕ}
    (hW : 0 < W) (hWv : W*W ≤ v) (hvN : v ≤ N) (hXN : X ≤ N)
    (he : 0 < e) (j : ℕ) {L Ep B : ℝ} (hL : 1 ≤ L) (hlog : Real.log N ≤ L-1)
    (hm : |reciprocalMoebius W| ≤ 1) (hB : 0 ≤ B)
    (hprime : |inputResidueRow α e j X-Chebyshev.psi X/e| ≤ Ep)
    (hdiv : ∀ Y ≤ N, ∀ d ∈ Ioc 0 v,
      |((residueDivisorPairs α Y d e j).card : ℝ)-(Y : ℝ)/(d*e)| ≤ B) :
    |total X (fun n =>
      (meanCenteredTypeII W W n-total N (fun n => meanCenteredTypeII W W n)/N)*
        centeredResidue α e j n)| ≤ Ep+40*(v : ℝ)*L^2*(B+1) := by
  have hh := centered_twisted_prefix_bound (centeredResidue α e j) hW hWv hvN hXN
    hL hlog hm (by positivity : 0 ≤ B+1) (centeredResidue_abs_le_one α he j)
    (by simpa only [centeredResidue_prime_sum] using hprime)
    (fun Y hY d hd => centeredResidue_divisor_bound α he j d Y (hdiv Y hY d hd))
  have hz : 0 ≤ (v : ℝ)*L^2*B := by positivity
  nlinarith only [hh, hz]

#print axioms centered_residue_remainder_prefix
end Erdos972ResidueRemainderPrefix
