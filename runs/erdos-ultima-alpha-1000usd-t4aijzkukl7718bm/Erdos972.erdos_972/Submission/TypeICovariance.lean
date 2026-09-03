import Submission.ProfileLogShift
import Submission.TypeISmallBounds

/-! A finite, two-sided covariance estimate for the actual Vaughan Type-I
parts, including the output logarithm and both small cutoff terms. -/
namespace Erdos972TypeICovariance

open Finset ArithmeticFunction
open Erdos972DivisorCovariance Erdos972LogarithmicCovariance Erdos972TypeIPolynomial
open Erdos972LogDivisorProfiles Erdos972CovariancePerturbation Erdos972ProfileLogShift
open Erdos972PrimePowerError Erdos972DivisorPairCount Erdos972Vaughan
open Erdos972DoubleVaughan Erdos972TypeISmallBounds Erdos972ChebyshevRowMean
open Erdos972MobiusPartialSums

set_option maxHeartbeats 1000000

lemma typeIPart_profile (U V : ℕ) (hV : 0 < V) {n : ℕ} (hn : 0 < n) :
    typeIPart U V n = profile (U*V) (slopeCoeff U) (constantCoeff U V) n+cutoff Λ V n :=
  typeIPart_polynomial U V hV hn

lemma typeI_profileMass_le {U V v : ℕ} (hDv : U*V ≤ v) {L : ℝ}
    (hL : 1 ≤ L) (hlog : Real.log (U*V : ℕ) ≤ L-1) :
    profileMass (U*V) (slopeCoeff U) (constantCoeff U V) ≤ 2*(v : ℝ)*L := by
  have ha := slopeCoeff_mass U (U*V)
  have hb := constantCoeff_mass U V (U*V)
  have hDvR : ((U*V : ℕ) : ℝ) ≤ v := Nat.cast_le.mpr hDv
  have hmul := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 2*((U*V : ℕ) : ℝ) by positivity)
  have hscale := mul_le_mul_of_nonneg_right hDvR (show 0 ≤ 2*L by linarith)
  unfold profileMass
  nlinarith only [ha, hb, hmul, hscale, Nat.cast_nonneg (α := ℝ) (U*V)]

lemma profile_abs_of_log_le (D : ℕ) (a b : ℕ → ℝ) (n : ℕ) {L : ℝ}
    (hL : 1 ≤ L) (hlog : Real.log n ≤ L-1) :
    |profile D a b n| ≤ L*profileMass D a b := by
  have ha := divisorPolynomial_abs_le D n a
  have hb := divisorPolynomial_abs_le D n b
  unfold profile
  apply (abs_add_le _ _).trans
  rw [abs_mul, abs_of_nonneg (Real.log_natCast_nonneg n)]
  have hh := mul_le_mul hlog ha (abs_nonneg _) (by linarith : 0 ≤ L-1)
  unfold profileMass
  nlinarith only [hh, hb, mul_nonneg (by linarith : 0 ≤ L-1) (coefficientMass_nonneg D b),
    coefficientMass_nonneg D a]

/-- A common finite bound. It separates the signed main term from the local
joint-divisibility discrepancy; no two-prime cancellation is assumed. -/
theorem typeI_covariance_bound {α : ℝ} (hα : 1 ≤ α) {N U V S T v : ℕ}
    (hU : 0 < U) (hV : 0 < V) (hS : 0 < S) (hT : 0 < T)
    (hDv : U*V ≤ v) (hEv : S*T ≤ v) (hvN : v ≤ N)
    {B : ℝ} (hB : 0 ≤ B)
    (hlocal : ∀ j ≤ N, ∀ a ∈ Ioc 0 (U*V), ∀ b ∈ Ioc 0 (S*T),
      |((divisorPairs α j a b).card : ℝ)-(j : ℝ)/(a*b)| ≤ B) :
    |covariance N (fun n => typeIPart U V n) (fun n => typeIPart S T (floorMul α n))| ≤
      32*(N : ℝ)*|reciprocalMoebius U*reciprocalMoebius S|+
        100*(B+1)*(v : ℝ)^2*(1+Real.log (α*N))^5 := by
  have hD : 0 < U*V := Nat.mul_pos hU hV
  have hE : 0 < S*T := Nat.mul_pos hS hT
  have hv : 0 < v := hD.trans_le hDv
  have hN : 0 < N := hv.trans_le hvN
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hvR : (1 : ℝ) ≤ v := by exact_mod_cast hv
  have hα0 : 0 < α := by linarith
  have hαN : (N : ℝ) ≤ α*N := le_mul_of_one_le_left hNR.le hα
  have hαN1 : 1 ≤ α*N := (by exact_mod_cast hN : (1 : ℝ) ≤ N).trans hαN
  let L : ℝ := 1+Real.log (α*N)
  have hL : 1 ≤ L := by dsimp [L]; linarith [Real.log_nonneg hαN1]
  have hL0 : 0 ≤ L := by linarith
  have hlogN : Real.log N ≤ L-1 := by
    dsimp [L]
    linarith only [Real.log_le_log hNR hαN]
  have hlogα : Real.log α ≤ L-1 := by
    have hh : α ≤ α*N := le_mul_of_one_le_right hα0.le (by exact_mod_cast hN)
    dsimp [L]
    linarith only [Real.log_le_log hα0 hh]
  have hlogD : Real.log (U*V : ℕ) ≤ L-1 :=
    (Erdos972ExponentialSum.monotone_log_natCast (hDv.trans hvN)).trans hlogN
  have hlogE : Real.log (S*T : ℕ) ≤ L-1 :=
    (Erdos972ExponentialSum.monotone_log_natCast (hEv.trans hvN)).trans hlogN
  have hM₁ := typeI_profileMass_le hDv hL hlogD
  have hM₂ := typeI_profileMass_le hEv hL hlogE
  let F := profile (U*V) (slopeCoeff U) (constantCoeff U V)
  let G := fun n => profile (S*T) (slopeCoeff S) (constantCoeff S T) (floorMul α n)
  have hF : ∀ n ∈ Ioc 0 N, |F n| ≤ 2*(v : ℝ)*L^2 := by
    intro n hn
    have hl := (log_input_le hn).trans hlogN
    have hh := (profile_abs_of_log_le (U*V) (slopeCoeff U) (constantCoeff U V) n hL hl).trans
      (mul_le_mul_of_nonneg_left hM₁ hL0)
    exact hh.trans_eq (by ring)
  have hG : ∀ n ∈ Ioc 0 N, |G n| ≤ 2*(v : ℝ)*L^2 := by
    intro n hn
    have hl : Real.log (floorMul α n) ≤ L-1 := by
      dsimp [L]
      linarith only [log_floorMul_le hα hn]
    have hh := (profile_abs_of_log_le (S*T) (slopeCoeff S) (constantCoeff S T) _ hL hl).trans
      (mul_le_mul_of_nonneg_left hM₂ hL0)
    exact hh.trans_eq (by ring)
  have hg : ∀ n ∈ Ioc 0 N, |typeIPart S T (floorMul α n)| ≤ 3*(v : ℝ)*L^2 := by
    intro n hn
    rw [typeIPart_profile S T hT (floorMul_pos hα (mem_Ioc.mp hn).1)]
    apply (abs_add_le _ _).trans
    rw [abs_of_nonneg (cutoff_vonMangoldt_nonneg _ _)]
    have hc := (cutoff_vonMangoldt_le T (floorMul α n)).trans
      (vonMangoldt_le_log.trans (log_floorMul_le hα hn))
    have h₁ : L ≤ (v : ℝ)*L^2 := by
      have hs : L ≤ L^2 := by nlinarith only [hL]
      exact hs.trans (le_mul_of_one_le_left (sq_nonneg L) hvR)
    have hgg := hG n hn
    dsimp [G] at hgg
    have hc' : cutoff Λ T (floorMul α n) ≤ L := hc.trans (by dsimp only [L]; linarith)
    linarith only [hc', h₁, hgg]
  have hsmall₁ : total N (fun n => |typeIPart U V n-F n|) ≤ 7*(v : ℝ) := by
    have he : total N (fun n => |typeIPart U V n-F n|) = ∑ n ∈ Ioc 0 N, cutoff Λ V n := by
      apply sum_congr rfl
      intro n hn
      change |typeIPart U V n-F n| = cutoff Λ V n
      rw [typeIPart_profile U V hV (mem_Ioc.mp hn).1]
      dsimp [F]
      rw [add_sub_cancel_left]
      exact abs_of_nonneg (cutoff_vonMangoldt_nonneg _ _)
    rw [he]
    have hVv : V ≤ v := (show V ≤ U*V by nlinarith).trans hDv
    exact (cutoff_mangoldt_sum_le V N).trans ((psi_le_seven_mul (Nat.cast_nonneg V)).trans
      (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hVv) (by norm_num)))
  have hsmall₂ : total N (fun n => |typeIPart S T (floorMul α n)-G n|) ≤ 7*(v : ℝ) := by
    have he : total N (fun n => |typeIPart S T (floorMul α n)-G n|) =
        ∑ n ∈ Ioc 0 N, cutoff Λ T (floorMul α n) := by
      apply sum_congr rfl
      intro n hn
      change |typeIPart S T (floorMul α n)-G n| = cutoff Λ T (floorMul α n)
      rw [typeIPart_profile S T hT (floorMul_pos hα (mem_Ioc.mp hn).1)]
      dsimp [G]
      rw [add_sub_cancel_left]
      exact abs_of_nonneg (cutoff_vonMangoldt_nonneg _ _)
    rw [he]
    have hTv : T ≤ v := (show T ≤ S*T by nlinarith).trans hEv
    exact (cutoff_mangoldt_output_sum_le hα T N).trans ((psi_le_seven_mul (Nat.cast_nonneg T)).trans
      (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hTv) (by norm_num)))
  have hpert := covariance_l1_perturb hN (fun n => typeIPart U V n)
    (fun n => typeIPart S T (floorMul α n)) F G hF hg
  have hpert' : |covariance N (fun n => typeIPart U V n)
      (fun n => typeIPart S T (floorMul α n))-covariance N F G| ≤ 70*(v : ℝ)^2*L^2 := by
    have h₁ := mul_le_mul_of_nonneg_left hsmall₁ (show 0 ≤ 2*(3*(v : ℝ)*L^2) by positivity)
    have h₂ := mul_le_mul_of_nonneg_left hsmall₂ (show 0 ≤ 2*(2*(v : ℝ)*L^2) by positivity)
    nlinarith only [hpert, h₁, h₂]
  have hbody := profile_covariance hα hN hD hE (slopeCoeff U) (constantCoeff U V)
    (slopeCoeff S) (constantCoeff S T) hB hlocal
  rw [slopeCoeff_mean (show U ≤ U*V by nlinarith), slopeCoeff_mean (show S ≤ S*T by nlinarith)] at hbody
  have hshift : profileMass (S*T) (slopeCoeff S)
      (fun k => Real.log α*slopeCoeff S k+constantCoeff S T k) ≤ 2*(v : ℝ)*L^2 := by
    have hs := profileMass_shift (S*T) (Real.log α) (slopeCoeff S) (constantCoeff S T)
    rw [abs_of_nonneg (Real.log_nonneg hα)] at hs
    have hh := mul_le_mul (show 1+Real.log α ≤ L by linarith only [hlogα]) hM₂
      (profileMass_nonneg _ _ _) hL0
    exact hs.trans (hh.trans_eq (by ring))
  have hcm : coefficientMass (S*T) (slopeCoeff S) ≤ (v : ℝ) :=
    (slopeCoeff_mass S (S*T)).trans (Nat.cast_le.mpr hEv)
  have hlogpow : (1+Real.log N)^2 ≤ L^2 :=
    pow_le_pow_left₀ (by linarith [Real.log_natCast_nonneg N]) (by linarith only [hlogN]) 2
  have h₁ : 6*(1+Real.log N)^2*B*profileMass (U*V) (slopeCoeff U) (constantCoeff U V)*
      profileMass (S*T) (slopeCoeff S) (fun k => Real.log α*slopeCoeff S k+constantCoeff S T k) ≤
        24*B*(v : ℝ)^2*L^5 := by
    have hh := mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hlogpow (by norm_num : (0 : ℝ) ≤ 6)) hB)
      hM₁ (profileMass_nonneg _ _ _) (by positivity)) hshift
      (profileMass_nonneg _ _ _) (by positivity)
    exact hh.trans_eq (by ring)
  have h₂ : 2*(1+Real.log N)^2*profileMass (U*V) (slopeCoeff U) (constantCoeff U V)*
      coefficientMass (S*T) (slopeCoeff S) ≤ 4*(v : ℝ)^2*L^3 := by
    have hh := mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hlogpow (by norm_num : (0 : ℝ) ≤ 2))
      hM₁ (profileMass_nonneg _ _ _) (by positivity)) hcm (coefficientMass_nonneg _ _) (by positivity)
    exact hh.trans_eq (by ring)
  have hL25 : L^2 ≤ L^5 := pow_le_pow_right₀ hL (by norm_num)
  have hL35 : L^3 ≤ L^5 := pow_le_pow_right₀ hL (by norm_num)
  have hrest : 24*B*(v : ℝ)^2*L^5+4*(v : ℝ)^2*L^3+70*(v : ℝ)^2*L^2 ≤
      100*(B+1)*(v : ℝ)^2*L^5 := by
    have hh₂ := mul_le_mul_of_nonneg_left hL25 (show 0 ≤ 70*(v : ℝ)^2 by positivity)
    have hh₃ := mul_le_mul_of_nonneg_left hL35 (show 0 ≤ 4*(v : ℝ)^2 by positivity)
    nlinarith only [hh₂, hh₃, mul_nonneg hB (show 0 ≤ (v : ℝ)^2*L^5 by positivity),
      show 0 ≤ (v : ℝ)^2*L^5 by positivity]
  have ht := abs_sub_le (covariance N (fun n => typeIPart U V n)
    (fun n => typeIPart S T (floorMul α n))) (covariance N F G) 0
  simp only [sub_zero] at ht
  change |covariance N F G| ≤ _ at hbody
  change _ ≤ 32*(N : ℝ)*|reciprocalMoebius U*reciprocalMoebius S|+100*(B+1)*(v : ℝ)^2*L^5
  linarith only [hbody, h₁, h₂, hpert', ht, hrest]

#print axioms typeI_covariance_bound

end Erdos972TypeICovariance
