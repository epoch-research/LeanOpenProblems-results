import Submission.FiniteFloorFourierBounds

/-! Quantitative parity-twisted prefix estimates for the actual recentered
remainder, from the existing dual prime rows and joint divisor counts. -/
namespace Erdos972ParityFloorPrefix

open Finset ArithmeticFunction
open scoped ArithmeticFunction.zeta
open Erdos972PrimePowerError Erdos972LogarithmicCovariance
open Erdos972DivisorMeanRecenter Erdos972RecenteredRemainderPrefix
open Erdos972RecenterCovarianceBounds Erdos972TypeISmallBounds Erdos972ChebyshevRowMean
open Erdos972Vaughan Erdos972DoubleVaughan Erdos972MobiusPartialSums
open Erdos972DivisorCovariance Erdos972DivisorPairCount Erdos972LogDivisorProfiles
open Erdos972TypeIPolynomial Erdos972TypeICovariance Erdos972DualPrimeRows

set_option maxHeartbeats 2000000

noncomputable def paritySign (n : ℕ) : ℝ := if 2 ∣ n then 1 else -1
noncomputable def parityCoeff (d : ℕ) : ℝ := if d = 1 then -1 else if d = 2 then 2 else 0

lemma abs_paritySign (n : ℕ) : |paritySign n| = 1 := by
  unfold paritySign
  split_ifs <;> norm_num

lemma parity_polynomial (n : ℕ) : divisorPolynomial 2 parityCoeff n = paritySign n := by
  have he : (Ioc 0 2 : Finset ℕ) = {1,2} := by decide
  by_cases hn : 2 ∣ n <;> norm_num [divisorPolynomial, he, parityCoeff, paritySign, hn]

lemma parity_mean : divisorMean 2 parityCoeff = 0 := by
  have he : (Ioc 0 2 : Finset ℕ) = {1,2} := by decide
  norm_num [divisorMean, he, parityCoeff]

lemma parity_mass : profileMass 2 (fun _ => 0) parityCoeff = 3 := by
  have he : (Ioc 0 2 : Finset ℕ) = {1,2} := by decide
  norm_num [profileMass, coefficientMass, he, parityCoeff]

lemma parity_aligned (α : ℝ) (n : ℕ) :
    alignedOutput α 2 (fun _ => 0) parityCoeff n = paritySign (floorMul α n) := by
  simp [alignedOutput, divisorPolynomial, ← parity_polynomial]

lemma parity_model (n : ℕ) : model 2 (fun _ => 0) parityCoeff n = 0 := by
  rw [model, parity_mean]
  simp [divisorMean]

lemma logTail_nonneg_le_log (V n : ℕ) : 0 ≤ logTail V n ∧ logTail V n ≤ Real.log n := by
  rw [logTail, mul_comm, ArithmeticFunction.coe_mul_zeta_apply]
  exact ⟨sum_nonneg (fun d hd => tail_vonMangoldt_nonneg V d),
    (sum_le_sum (fun d hd => tail_vonMangoldt_le V d)).trans_eq vonMangoldt_sum⟩

lemma meanCenteredTypeII_abs_bound {U V v n : ℕ} (hU : 0 < U) (hV : 0 < V)
    (hUV : U*V ≤ v) (hn : 0 < n) {L : ℝ} (hL : 1 ≤ L)
    (hlogD : Real.log (U*V : ℕ) ≤ L-1) (hlogn : Real.log n ≤ L-1)
    (hm : |reciprocalMoebius U| ≤ 1) :
    |meanCenteredTypeII U V n| ≤ 5*(v : ℝ)*L^2 := by
  have hR := typeII_abs_of_log_bound hU hV hUV hn hL hlogD hlogn
  have htail := logTail_nonneg_le_log V n
  have hcorr : |reciprocalMoebius U*logTail V n| ≤ Real.log n := by
    rw [abs_mul, abs_of_nonneg htail.1]
    exact (mul_le_mul_of_nonneg_right hm htail.1).trans (by simpa using htail.2)
  rw [meanCenteredTypeII_eq, ArithmeticFunction.add_apply, pointScale_apply]
  have hh := abs_add_le (typeIIPart U V n) (reciprocalMoebius U*logTail V n)
  have hv : (1 : ℝ) ≤ v := by exact_mod_cast (Nat.mul_pos hU hV).trans_le hUV
  have hVL : L ≤ (v : ℝ)*L^2 := by
    have hl : L ≤ L^2 := by nlinarith only [hL]
    exact hl.trans (le_mul_of_one_le_left (sq_nonneg L) hv)
  linarith only [hh, hR, hcorr, hlogn, hVL]

lemma parity_prime_sum (α : ℝ) (X : ℕ) :
    total X (fun n => vonMangoldt n*paritySign (floorMul α n)) =
      2*inputDivisorRow α 2 X-Chebyshev.psi X := by
  have hp (n : ℕ) : vonMangoldt n*paritySign (floorMul α n) =
      2*(if 2 ∣ floorMul α n then vonMangoldt n else 0)-vonMangoldt n := by
    unfold paritySign
    split_ifs <;> ring
  simp only [total, hp, sum_sub_distrib, ← mul_sum, inputDivisorRow, sum_filter,
    Chebyshev.psi, Nat.floor_natCast]

lemma parity_prime_bound {α : ℝ} {X : ℕ} {E : ℝ}
    (h : |inputDivisorRow α 2 X-Chebyshev.psi X/2| ≤ E) :
    |total X (fun n => vonMangoldt n*paritySign (floorMul α n))| ≤ 2*E := by
  rw [parity_prime_sum,
    show 2*inputDivisorRow α 2 X-Chebyshev.psi X =
      2*(inputDivisorRow α 2 X-Chebyshev.psi X/2) by ring, abs_mul]
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact mul_le_mul_of_nonneg_left h (by norm_num)

lemma parity_profile_bound (α : ℝ) {U V v N X : ℕ}
    (hUV : U*V ≤ v) (hvN : v ≤ N) (hXN : X ≤ N) {L Bd : ℝ}
    (hL : 1 ≤ L) (hlog : Real.log N ≤ L-1) (hBd : 0 ≤ Bd)
    (hdiv : ∀ j ≤ N, ∀ a ∈ Ioc 0 v, ∀ b ∈ Ioc 0 2,
      |((divisorPairs α j a b).card : ℝ)-(j : ℝ)/(a*b)| ≤ Bd) :
    |total X (fun n => profile (U*V) (slopeCoeff U) (constantCoeff U V) n*
      paritySign (floorMul α n))| ≤ 12*(v : ℝ)*L^3*Bd := by
  have hh := profile_pair_first_moment α X (U*V) 2 (slopeCoeff U) (constantCoeff U V)
    (fun _ => 0) parityCoeff hBd (by
      intro j hj a ha b hb
      exact hdiv j (hj.trans hXN) a (mem_Ioc.mpr ⟨(mem_Ioc.mp ha).1, (mem_Ioc.mp ha).2.trans hUV⟩) b hb)
  simp only [parity_aligned, parity_model, mul_zero, total, sum_const_zero, sub_zero, parity_mass] at hh
  have hm := typeI_profileMass_le hUV hL
    ((Erdos972ExponentialSum.monotone_log_natCast (hUV.trans hvN)).trans hlog)
  have hx : 1+Real.log X ≤ L := by
    linarith only [(Erdos972ExponentialSum.monotone_log_natCast hXN).trans hlog]
  have hp := pow_le_pow_left₀ (by positivity [Real.log_natCast_nonneg X]) hx 2
  have hb := mul_le_mul hp hm (profileMass_nonneg _ _ _) (sq_nonneg L)
  have hb' := mul_le_mul_of_nonneg_left hb (show 0 ≤ 6*Bd by positivity)
  unfold total
  nlinarith only [hh, hb']

lemma parity_total_bound (α : ℝ) {v N X : ℕ} (hv : 0 < v) (hXN : X ≤ N)
    {L Bd : ℝ} (hL : 1 ≤ L) (hlog : Real.log N ≤ L-1) (hBd : 0 ≤ Bd)
    (hdiv : ∀ j ≤ N, ∀ a ∈ Ioc 0 v, ∀ b ∈ Ioc 0 2,
      |((divisorPairs α j a b).card : ℝ)-(j : ℝ)/(a*b)| ≤ Bd) :
    |total X (fun n => paritySign (floorMul α n))| ≤ 6*L*Bd := by
  have hh := aligned_first_moment α (N := X) (D := 1) (E := 2) (by norm_num)
    (fun _ => 0) parityCoeff hBd (by
      intro j hj a ha b hb
      exact hdiv j (hj.trans hXN) a (mem_Ioc.mpr ⟨(mem_Ioc.mp ha).1, (mem_Ioc.mp ha).2.trans hv⟩) b hb)
  simp only [parity_aligned, parity_model, total, sum_const_zero, sub_zero, parity_mass] at hh
  have hx : 1+Real.log X ≤ L := by
    linarith only [(Erdos972ExponentialSum.monotone_log_natCast hXN).trans hlog]
  unfold total
  nlinarith only [hh, mul_le_mul_of_nonneg_right hx hBd]

/-- All prefix errors are controlled by the very same dual and joint rows.
In particular the global empirical mean in the input is not omitted. -/
theorem centered_parity_prefix_bound (α : ℝ) {W v N X : ℕ}
    (hW : 0 < W) (hWv : W*W ≤ v) (hvN : v ≤ N) (hXN : X ≤ N)
    {L Ep Bd : ℝ} (hL : 1 ≤ L) (hlog : Real.log N ≤ L-1)
    (hm : |reciprocalMoebius W| ≤ 1) (hBd : 0 ≤ Bd)
    (hprime : ∀ j ≤ N, |inputDivisorRow α 2 j-Chebyshev.psi j/2| ≤ Ep)
    (hdiv : ∀ j ≤ N, ∀ a ∈ Ioc 0 v, ∀ b ∈ Ioc 0 2,
      |((divisorPairs α j a b).card : ℝ)-(j : ℝ)/(a*b)| ≤ Bd) :
    |total X (fun n =>
      (meanCenteredTypeII W W n-total N (fun n => meanCenteredTypeII W W n)/N)*
        paritySign (floorMul α n))| ≤ 2*Ep+64*(v : ℝ)*L^3*(Bd+1) := by
  have hWv' : W ≤ v := (show W ≤ W*W by nlinarith only [hW]).trans hWv
  have hv : 0 < v := hW.trans_le hWv'
  have hN : 0 < N := hv.trans_le hvN
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hL0 : 0 ≤ L := by linarith only [hL]
  let R := fun n => meanCenteredTypeII W W n
  let P := fun n => paritySign (floorMul α n)
  let A := profile (W*W) (slopeCoeff W) (constantCoeff W W)
  let B := profile (1*W) (slopeCoeff 1) (constantCoeff 1 W)
  have hA := parity_profile_bound α hWv hvN hXN hL hlog hBd hdiv
  have hB := parity_profile_bound α (U := 1) (V := W)
    (by simpa only [one_mul] using hWv') hvN hXN hL hlog hBd hdiv
  have hs : |total X (fun n => cutoff vonMangoldt W n*P n)| ≤ 7*(v : ℝ) := by
    have hh := abs_sum_le_sum_abs (fun n => cutoff vonMangoldt W n*P n) (Ioc 0 X)
    simp only [abs_mul, P, abs_paritySign, mul_one,
      abs_of_nonneg (cutoff_vonMangoldt_nonneg _ _)] at hh
    exact hh.trans ((cutoff_mangoldt_sum_le W X).trans
      ((psi_le_seven_mul (Nat.cast_nonneg W)).trans
        (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hWv') (by norm_num))))
  have hR (n : ℕ) (hn : 0 < n) : R n = vonMangoldt n-A n+reciprocalMoebius W*B n-cutoff vonMangoldt W n := by
    have hh := congrArg (fun f : ArithmeticFunction ℝ => f n) (mean_centered_vaughan_identity W W)
    dsimp only at hh
    rw [ArithmeticFunction.add_apply, meanCenteredTypeI_profile hW hn] at hh
    dsimp only [R, A, B]
    linarith only [hh]
  have hsum : total X (fun n => R n*P n) =
      total X (fun n => vonMangoldt n*P n)-total X (fun n => A n*P n)+
        reciprocalMoebius W*total X (fun n => B n*P n)-
          total X (fun n => cutoff vonMangoldt W n*P n) := by
    simp only [total, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro n hn
    rw [hR n (mem_Ioc.mp hn).1]
    ring
  change |total X (fun n => B n*P n)| ≤ 12*(v : ℝ)*L^3*Bd at hB
  have hBm : |reciprocalMoebius W*total X (fun n => B n*P n)| ≤ 12*(v : ℝ)*L^3*Bd := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right hm (abs_nonneg _)).trans
      (by simpa only [one_mul] using hB)
  have hraw : |total X (fun n => R n*P n)| ≤ 2*Ep+24*(v : ℝ)*L^3*Bd+7*v := by
    rw [hsum]
    apply ((abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans
      (add_le_add (abs_sub _ _) le_rfl)) le_rfl)).trans
    have hp := parity_prime_bound (hprime X hXN)
    linarith only [hp, hA, hBm, hs]
  have hpoint (n : ℕ) (hn : n ∈ Ioc 0 N) : |R n| ≤ 5*(v : ℝ)*L^2 := by
    exact meanCenteredTypeII_abs_bound hW hW hWv (mem_Ioc.mp hn).1 hL
      ((Erdos972ExponentialSum.monotone_log_natCast (hWv.trans hvN)).trans hlog)
      ((Erdos972ExponentialSum.monotone_log_natCast (mem_Ioc.mp hn).2).trans hlog) hm
  have hmean : |total N R/(N : ℝ)| ≤ 5*(v : ℝ)*L^2 := by
    rw [abs_div, abs_of_pos hNR]
    apply (div_le_iff₀ hNR).mpr
    simpa only [mul_comm] using total_abs_le hpoint
  have hp := parity_total_bound α hv hXN hL hlog hBd hdiv
  have hcorr : |(total N R/N)*total X P| ≤ 30*(v : ℝ)*L^3*Bd := by
    rw [abs_mul]
    have hh := mul_le_mul hmean hp (abs_nonneg _) (show 0 ≤ 5*(v : ℝ)*L^2 by positivity)
    exact hh.trans_eq (by ring)
  have he : total X (fun n => (R n-total N R/N)*P n) =
      total X (fun n => R n*P n)-(total N R/N)*total X P := by
    simp only [total, sub_mul, sum_sub_distrib, mul_sum]
  change |total X (fun n => (R n-total N R/N)*P n)| ≤ _
  rw [he]
  apply (abs_sub _ _).trans
  have hvL : 7*(v : ℝ) ≤ 7*(v : ℝ)*L^3 :=
    le_mul_of_one_le_right (by positivity) (one_le_pow₀ hL)
  have hpos : 0 ≤ (v : ℝ)*L^3*Bd := by positivity
  have hpos' : 0 ≤ (v : ℝ)*L^3 := by positivity
  nlinarith only [hraw, hcorr, hvL, hpos, hpos']

#print axioms meanCenteredTypeII_abs_bound
#print axioms centered_parity_prefix_bound

end Erdos972ParityFloorPrefix
