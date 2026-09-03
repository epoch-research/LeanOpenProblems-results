import Submission.RecenterCovarianceScales

/-! Finite prefix estimates for the recentered arithmetic remainder. The
logarithmic profile slopes cancel before any Mertens rate is used. -/
namespace Erdos972RecenteredRemainderPrefix

open Finset ArithmeticFunction
open Erdos972PrimePowerError Erdos972LogarithmicCovariance
open Erdos972DivisorMeanRecenter Erdos972RecenterCovarianceScales
open Erdos972TypeICovariance Erdos972TypeIPolynomial Erdos972LogDivisorProfiles
open Erdos972DivisorPairCount Erdos972DivisorCovariance Erdos972MobiusPartialSums
open Erdos972Vaughan Erdos972TypeISmallBounds Erdos972ChebyshevRowMean

set_option maxHeartbeats 1500000

lemma divisorPairs_one_card (α : ℝ) (N : ℕ) {d : ℕ} (hd : 0 < d) :
    (divisorPairs α N d 1).card = N/d := by
  have hh := divisorPairs_card_add_one α N d 1 hd
  simp only [Erdos972RationalRotationCount.divisorRow, one_dvd, filter_true, card_range] at hh
  omega

lemma divisorPairs_one_error (α : ℝ) (N : ℕ) {d : ℕ} (hd : 0 < d) :
    |((divisorPairs α N d 1).card : ℝ)-(N : ℝ)/(d*1)| ≤ 1 := by
  rw [divisorPairs_one_card α N hd, mul_one, abs_sub_comm,
    abs_of_nonneg (sub_nonneg.mpr Nat.cast_div_le)]
  have hh := Nat.lt_floor_add_one ((N : ℝ)/d)
  rw [Nat.floor_div_natCast, Nat.floor_natCast] at hh
  linarith only [hh]

lemma ordinary_profile_first_moment (N D : ℕ) (a b : ℕ → ℝ) :
    |total N (profile D a b)-total N (model D a b)| ≤
      2*(1+Real.log N)*profileMass D a b := by
  have hh := profile_first_moment (1 : ℝ) (N := N) (D := D) (E := 1) (by norm_num) a b (by norm_num : (0 : ℝ) ≤ 1)
    (by
      intro j hj d hd e he
      have he1 : e = 1 := by have := mem_Ioc.mp he; omega
      subst e
      simpa only [Nat.cast_one] using divisorPairs_one_error 1 j (mem_Ioc.mp hd).1)
  simpa only [mul_one] using hh

noncomputable def recenteredConstant (U V : ℕ) : ℝ :=
  divisorMean (U*V) (constantCoeff U V)-
    reciprocalMoebius U*divisorMean (1*V) (constantCoeff 1 V)

lemma meanCenteredTypeI_profile {U V n : ℕ} (hV : 0 < V) (hn : 0 < n) :
    meanCenteredTypeI U V n = profile (U*V) (slopeCoeff U) (constantCoeff U V) n-
      reciprocalMoebius U*profile (1*V) (slopeCoeff 1) (constantCoeff 1 V) n+
      cutoff vonMangoldt V n := by
  rw [meanCenteredTypeI, Erdos972Vaughan.sub_apply, pointScale_apply, logTail_typeI,
    Erdos972Vaughan.sub_apply, typeIPart_profile U V hV hn,
    typeIPart_profile 1 V hV hn]
  ring

lemma recentered_model_constant {U V : ℕ} (hV : 0 < V) (n : ℕ) :
    model (U*V) (slopeCoeff U) (constantCoeff U V) n-
      reciprocalMoebius U*model (1*V) (slopeCoeff 1) (constantCoeff 1 V) n =
        recenteredConstant U V := by
  have hU : U ≤ U*V := by nlinarith only [hV]
  simp only [model]
  rw [slopeCoeff_mean hU, slopeCoeff_mean (show 1 ≤ 1*V by omega), reciprocalMoebius_one]
  unfold recenteredConstant
  ring

lemma typeI_profile_prefix_error {U V v N X : ℕ} (hU : 0 < U) (hV : 0 < V)
    (hUV : U*V ≤ v) (hvN : v ≤ N) (hXN : X ≤ N) {L : ℝ}
    (hL : 1 ≤ L) (hlog : Real.log N ≤ L-1) :
    |total X (profile (U*V) (slopeCoeff U) (constantCoeff U V))-
      total X (model (U*V) (slopeCoeff U) (constantCoeff U V))| ≤ 4*(v : ℝ)*L^2 := by
  have hm := typeI_profileMass_le hUV hL
    ((Erdos972ExponentialSum.monotone_log_natCast (hUV.trans hvN)).trans hlog)
  have hx : 1+Real.log X ≤ L := by
    linarith only [(Erdos972ExponentialSum.monotone_log_natCast hXN).trans hlog]
  have hh := ordinary_profile_first_moment X (U*V) (slopeCoeff U) (constantCoeff U V)
  have hmul := mul_le_mul hx hm (profileMass_nonneg _ _ _)
    (show 0 ≤ L by linarith only [hL])
  nlinarith only [hh, hmul]

/-- The full recentered Type-I prefix has a constant model. In particular,
there is no surviving factor m(U)*log N multiplying a mean error. -/
theorem recentered_typeI_prefix {U V v N X : ℕ} (hU : 0 < U) (hV : 0 < V)
    (hUV : U*V ≤ v) (hvN : v ≤ N) (hXN : X ≤ N) {L : ℝ}
    (hL : 1 ≤ L) (hlog : Real.log N ≤ L-1)
    (hm : |reciprocalMoebius U| ≤ 1) :
    |total X (fun n => meanCenteredTypeI U V n)-(X : ℝ)*recenteredConstant U V| ≤
      15*(v : ℝ)*L^2 := by
  have hVv : V ≤ v := (show V ≤ U*V by nlinarith only [hU]).trans hUV
  have he₁ := typeI_profile_prefix_error hU hV hUV hvN hXN hL hlog
  have he₂ := typeI_profile_prefix_error (U := 1) (by norm_num) hV
    (by simpa only [one_mul] using hVv) hvN hXN hL hlog
  let A := profile (U*V) (slopeCoeff U) (constantCoeff U V)
  let B := profile (1*V) (slopeCoeff 1) (constantCoeff 1 V)
  let a := model (U*V) (slopeCoeff U) (constantCoeff U V)
  let b := model (1*V) (slopeCoeff 1) (constantCoeff 1 V)
  have hmodels : total X a-reciprocalMoebius U*total X b =
      (X : ℝ)*recenteredConstant U V := by
    rw [show total X a-reciprocalMoebius U*total X b =
      total X (fun n => a n-reciprocalMoebius U*b n) by
        simp only [total, sum_sub_distrib, mul_sum]]
    simp only [a, b, recentered_model_constant hV, total, sum_const,
      Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul]
  have hsum : total X (fun n => meanCenteredTypeI U V n) =
      total X A-reciprocalMoebius U*total X B+total X (fun n => cutoff vonMangoldt V n) := by
    simp only [total, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro n hn
    exact meanCenteredTypeI_profile hV (mem_Ioc.mp hn).1
  have hs0 : 0 ≤ total X (fun n => cutoff vonMangoldt V n) := by
    exact sum_nonneg (fun n _ => cutoff_vonMangoldt_nonneg V n)
  have hsmall : total X (fun n => cutoff vonMangoldt V n) ≤ 7*(v : ℝ) :=
    (cutoff_mangoldt_sum_le V X).trans
      ((psi_le_seven_mul (Nat.cast_nonneg V)).trans
        (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hVv) (by norm_num)))
  change |total X B-total X b| ≤ 4*(v : ℝ)*L^2 at he₂
  have hsm : |reciprocalMoebius U*(total X B-total X b)| ≤ 4*(v : ℝ)*L^2 := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right hm (abs_nonneg _)).trans
      (by simpa only [one_mul] using he₂)
  have he : total X (fun n => meanCenteredTypeI U V n)-(X : ℝ)*recenteredConstant U V =
      ((total X A-total X a)-reciprocalMoebius U*(total X B-total X b))+
        total X (fun n => cutoff vonMangoldt V n) := by
    rw [hsum, ← hmodels]
    ring
  rw [he]
  have hh : |((total X A-total X a)-reciprocalMoebius U*(total X B-total X b))+
      total X (fun n => cutoff vonMangoldt V n)| ≤
      |total X A-total X a|+|reciprocalMoebius U*(total X B-total X b)|+
        total X (fun n => cutoff vonMangoldt V n) := by
    apply ((abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)).trans_eq
    rw [abs_of_nonneg hs0]
  have hpow : 1 ≤ L^2 := one_le_pow₀ hL
  have hvpow := mul_le_mul_of_nonneg_left hpow (show 0 ≤ 7*(v : ℝ) by positivity)
  change |total X A-total X a| ≤ 4*(v : ℝ)*L^2 at he₁
  linarith only [hh, he₁, hsm, hsmall, hvpow]

/-- The actual arithmetic remainder, with its constant model retained. -/
theorem recentered_remainder_prefix {U V v N X : ℕ} (hU : 0 < U) (hV : 0 < V)
    (hUV : U*V ≤ v) (hvN : v ≤ N) (hXN : X ≤ N) {L : ℝ}
    (hL : 1 ≤ L) (hlog : Real.log N ≤ L-1)
    (hm : |reciprocalMoebius U| ≤ 1) :
    |total X (fun n => meanCenteredTypeII U V n)-
      (Chebyshev.psi X-(X : ℝ)*recenteredConstant U V)| ≤ 15*(v : ℝ)*L^2 := by
  have hsum : total X (fun n => meanCenteredTypeII U V n) =
      Chebyshev.psi X-total X (fun n => meanCenteredTypeI U V n) := by
    have hh := congrArg (fun f : ArithmeticFunction ℝ => total X (fun n => f n))
      (mean_centered_vaughan_identity U V)
    simp only [ArithmeticFunction.add_apply, total, sum_add_distrib] at hh
    simp only [Chebyshev.psi, Nat.floor_natCast, total]
    linarith only [hh]
  rw [hsum, show Chebyshev.psi X-total X (fun n => meanCenteredTypeI U V n)-
      (Chebyshev.psi X-(X : ℝ)*recenteredConstant U V) =
      -(total X (fun n => meanCenteredTypeI U V n)-(X : ℝ)*recenteredConstant U V) by ring,
    abs_neg]
  exact recentered_typeI_prefix hU hV hUV hvN hXN hL hlog hm

/-- Removing the empirical mean cancels the constant model as well. -/
theorem centered_remainder_prefix {U V v N X : ℕ} (hU : 0 < U) (hV : 0 < V)
    (hUV : U*V ≤ v) (hvN : v ≤ N) (hXN : X ≤ N) {L : ℝ}
    (hL : 1 ≤ L) (hlog : Real.log N ≤ L-1)
    (hm : |reciprocalMoebius U| ≤ 1) :
    |total X (fun n => meanCenteredTypeII U V n)-
      (X : ℝ)/N*total N (fun n => meanCenteredTypeII U V n)| ≤
        |Chebyshev.psi X-(X : ℝ)/N*Chebyshev.psi N|+30*(v : ℝ)*L^2 := by
  have hN : 0 < N := (Nat.mul_pos hU hV).trans_le (hUV.trans hvN)
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hratio : (X : ℝ)/N ≤ 1 := (div_le_one hNR).mpr (Nat.cast_le.mpr hXN)
  have heX := recentered_remainder_prefix hU hV hUV hvN hXN hL hlog hm
  have heN := recentered_remainder_prefix hU hV hUV hvN le_rfl hL hlog hm
  let R := fun n => meanCenteredTypeII U V n
  let C := recenteredConstant U V
  have hscaled : |(X : ℝ)/N*(total N R-(Chebyshev.psi N-(N : ℝ)*C))| ≤ 15*(v : ℝ)*L^2 := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (X : ℝ)/N)]
    exact (mul_le_mul_of_nonneg_right hratio (abs_nonneg _)).trans
      (by simpa only [one_mul] using heN)
  have he : total X R-(X : ℝ)/N*total N R =
      (Chebyshev.psi X-(X : ℝ)/N*Chebyshev.psi N)+
      ((total X R-(Chebyshev.psi X-(X : ℝ)*C))-
        (X : ℝ)/N*(total N R-(Chebyshev.psi N-(N : ℝ)*C))) := by
    field_simp
    ring
  change |total X R-(X : ℝ)/N*total N R| ≤ _
  rw [he]
  apply ((abs_add_le _ _).trans (add_le_add le_rfl (abs_sub _ _))).trans
  linarith only [heX, hscaled]

#print axioms recentered_typeI_prefix
#print axioms recentered_remainder_prefix
#print axioms centered_remainder_prefix

end Erdos972RecenteredRemainderPrefix
