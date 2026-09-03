import Submission.DivisorMeanRecenter

/-! Finite bounds for the complete arithmetic recentering correction.
All mixed covariances and small cutoff terms are retained. -/
namespace Erdos972RecenterCovarianceBounds

open Finset ArithmeticFunction
open scoped ArithmeticFunction.zeta ArithmeticFunction.Moebius
open Erdos972DivisorMeanRecenter Erdos972LogarithmicCovariance
open Erdos972CovariancePerturbation Erdos972CenteredDoubleVaughan
open Erdos972Vaughan Erdos972DoubleVaughan Erdos972PrimePowerError
open Erdos972OriginalTypeICovariance Erdos972TypeISmallBounds
open Erdos972ChebyshevRowMean Erdos972MobiusPartialSums

set_option autoImplicit false
set_option maxHeartbeats 2000000

lemma abs_add_scaled_le {r b m A B : ℝ} (hm : |m| ≤ 1)
    (hr : |r| ≤ A) (hb : |b| ≤ B) : |r+m*b| ≤ A+B := by
  have hh := mul_le_mul_of_nonneg_right hm (abs_nonneg b)
  have ht := abs_add_le r (m*b)
  rw [abs_mul] at ht
  linarith only [ht, hr, hb, hh]

lemma small_scaled_difference_total (R B s : ℕ → ℝ) {m K : ℝ} (hm : |m| ≤ 1)
    (N : ℕ) (hs : total N (fun n => |s n|) ≤ K) :
    total N (fun n => |R n+m*(B n-s n)-(R n+m*B n)|) ≤ K := by
  have he (n : ℕ) : R n+m*(B n-s n)-(R n+m*B n) = -m*s n := by ring
  simp only [he, abs_mul, abs_neg, total, ← mul_sum]
  exact (mul_le_mul_of_nonneg_right hm (sum_nonneg (fun n hn => abs_nonneg (s n)))).trans
    (by simpa only [one_mul, total] using hs)

lemma recenter_small_cutoff_error {N : ℕ} (hN : 0 < N)
    (R Q B C s z : ℕ → ℝ) {m A Bcap Ccap K : ℝ}
    (hm : |m| ≤ 1) (hA : 0 ≤ A) (hB : 0 ≤ Bcap) (hC : 0 ≤ Ccap)
    (hR : ∀ n ∈ Ioc 0 N, |R n| ≤ A) (hQ : ∀ n ∈ Ioc 0 N, |Q n| ≤ A)
    (hBs : ∀ n ∈ Ioc 0 N, |B n| ≤ Bcap) (hCs : ∀ n ∈ Ioc 0 N, |C n| ≤ Bcap)
    (hz : ∀ n ∈ Ioc 0 N, |z n| ≤ Ccap)
    (hsum : total N (fun n => |s n|) ≤ K) (hzsum : total N (fun n => |z n|) ≤ K) :
    |covariance N (fun n => R n+m*(B n-s n)) (fun n => Q n+m*(C n-z n))-
      covariance N (fun n => R n+m*B n) (fun n => Q n+m*C n)| ≤
        2*K*(2*A+2*Bcap+Ccap) := by
  have hF (n : ℕ) (hn : n ∈ Ioc 0 N) : |R n+m*B n| ≤ A+Bcap :=
    abs_add_scaled_le hm (hR n hn) (hBs n hn)
  have hg (n : ℕ) (hn : n ∈ Ioc 0 N) : |Q n+m*(C n-z n)| ≤ A+Bcap+Ccap := by
    have hh := abs_add_scaled_le hm (hQ n hn)
      ((abs_sub _ _).trans (add_le_add (hCs n hn) (hz n hn)))
    linarith only [hh]
  have he := covariance_l1_perturb hN
    (fun n => R n+m*(B n-s n)) (fun n => Q n+m*(C n-z n))
    (fun n => R n+m*B n) (fun n => Q n+m*C n) hF hg
  have hs := mul_le_mul_of_nonneg_left (small_scaled_difference_total R B s hm N hsum)
    (show 0 ≤ 2*(A+Bcap+Ccap) by positivity)
  have hz' := mul_le_mul_of_nonneg_left (small_scaled_difference_total Q C z hm N hzsum)
    (show 0 ≤ 2*(A+Bcap) by positivity)
  nlinarith only [he, hs, hz']

lemma recenter_linear_error (N : ℕ) (R Q B C : ℕ → ℝ) (m : ℝ) :
    |covariance N (fun n => R n+m*B n) (fun n => Q n+m*C n)-covariance N R Q| ≤
      |m| *(|covariance N B Q|+|covariance N R C|)+m^2*|covariance N B C| := by
  rw [covariance_linear_expand]
  have he : covariance N R Q+m*covariance N B Q+m*covariance N R C+
      (m*m)*covariance N B C-covariance N R Q =
      (m*covariance N B Q+m*covariance N R C)+(m*m)*covariance N B C := by ring
  rw [he]
  apply (abs_add_le _ _).trans
  have hh := abs_add_le (m*covariance N B Q) (m*covariance N R C)
  simp only [abs_mul, ← pow_two, abs_sq] at hh ⊢
  nlinarith only [hh]

lemma weighted_three_errors {m a b c E₁ E₂ X E : ℝ}
    (hm : |m| ≤ 1) (h₁ : 0 ≤ E₁) (h₂ : 0 ≤ E₂) (hE : 0 ≤ E)
    (ha : |a| ≤ E₁+X*|m|+E) (hb : |b| ≤ E₂+X*|m|+E) (hc : |c| ≤ X+E) :
    |m| *(|a|+|b|)+m^2*|c| ≤ E₁+E₂+3*(X*m^2+E) := by
  have hsq : m^2 ≤ 1 := by nlinarith only [hm, sq_abs m, abs_nonneg m]
  have hsum := mul_le_mul_of_nonneg_left (add_le_add ha hb) (abs_nonneg m)
  have hlast := mul_le_mul_of_nonneg_left hc (sq_nonneg m)
  have hE1 := mul_le_mul_of_nonneg_right hm h₁
  have hE2 := mul_le_mul_of_nonneg_right hm h₂
  have hEE := mul_le_mul_of_nonneg_right hm hE
  have hEsq := mul_le_mul_of_nonneg_right hsq hE
  have he : |m| *(E₁+X*|m|+E+(E₂+X*|m|+E))+m^2*(X+E) =
      |m| *E₁+|m| *E₂+3*X*m^2+2*|m| *E+m^2*E := by
    calc
      _ = |m| *E₁+|m| *E₂+2*X*|m|^2+X*m^2+2*|m| *E+m^2*E := by ring
      _ = _ := by rw [sq_abs]; ring
  linarith only [hsum, hlast, hE1, hE2, hEE, hEsq, he]

lemma typeII_eq_mangoldt_sub_typeI (U V : ℕ) (n : ℕ) :
    typeIIPart U V n = vonMangoldt n-typeIPart U V n := by
  have hh := congrArg (fun f : ArithmeticFunction ℝ => f n) (mangoldt_split U V)
  simp only [ArithmeticFunction.add_apply] at hh
  linarith only [hh]

lemma typeII_abs_of_log_bound {U V v n : ℕ}
    (hU : 0 < U) (hV : 0 < V) (hUv : U*V ≤ v) (hn : 0 < n)
    {L : ℝ} (hL : 1 ≤ L) (hlogD : Real.log (U*V : ℕ) ≤ L-1)
    (hlogn : Real.log n ≤ L-1) : |typeIIPart U V n| ≤ 4*(v : ℝ)*L^2 := by
  have ha := typeIPart_abs_bound hU hV hUv hn hL hlogD hlogn
  have hv : (1 : ℝ) ≤ v := by exact_mod_cast (Nat.mul_pos hU hV).trans_le hUv
  have hVL : L ≤ (v : ℝ)*L^2 := by
    have hs : L ≤ L^2 := by nlinarith only [hL]
    exact hs.trans (le_mul_of_one_le_left (sq_nonneg L) hv)
  rw [typeII_eq_mangoldt_sub_typeI]
  have hh := abs_sub (vonMangoldt n) (typeIPart U V n)
  rw [abs_of_nonneg vonMangoldt_nonneg] at hh
  have hl := (vonMangoldt_le_log (n := n)).trans hlogn
  linarith only [hh, ha, hl, hVL]

lemma covariance_sub_left_recenter (N : ℕ) (f g h : ℕ → ℝ) :
    covariance N (fun n => f n-g n) h = covariance N f h-covariance N g h := by
  simp only [covariance, total, sub_mul, sum_sub_distrib]
  ring

/-- The complete finite correction estimate. Its hypotheses are the
original, dual, and joint Type-I covariance bounds, not a new signed-tail
or prime-pair estimate. -/
theorem mean_recenter_covariance_bound {α : ℝ} (hα : 1 ≤ α) {N W v : ℕ}
    (hW : 0 < W) (hWv : W*W ≤ v) (hvN : v ≤ N) {L : ℝ}
    (hL : 1 ≤ L) (hLN : Real.log N ≤ L-1) (hLg : Real.log (floorMul α N) ≤ L-1)
    (hm : |reciprocalMoebius W| ≤ 1) {E₁ E₂ E : ℝ} (hE : 0 ≤ E)
    (hleft : |covariance N (fun n => typeIPart 1 W n)
      (fun n => vonMangoldt (floorMul α n))| ≤ E₁)
    (hright : |covariance N (fun n => vonMangoldt n)
      (fun n => typeIPart 1 W (floorMul α n))| ≤ E₂)
    (hBA : |covariance N (fun n => typeIPart 1 W n)
      (fun n => typeIPart W W (floorMul α n))| ≤ 32*(N : ℝ)*|reciprocalMoebius W|+E)
    (hAB : |covariance N (fun n => typeIPart W W n)
      (fun n => typeIPart 1 W (floorMul α n))| ≤ 32*(N : ℝ)*|reciprocalMoebius W|+E)
    (hBB : |covariance N (fun n => typeIPart 1 W n)
      (fun n => typeIPart 1 W (floorMul α n))| ≤ 32*(N : ℝ)+E) :
    |meanCenteredFourFactor α N W W W W-centeredFourFactor α N W W W W| ≤
      E₁+E₂+96*(N : ℝ)*(reciprocalMoebius W)^2+3*E+210*(v : ℝ)^2*L^2 := by
  have hWv' : W ≤ v := (show W ≤ W*W by nlinarith).trans hWv
  have hN : 0 < N := (hW.trans_le hWv').trans_le hvN
  have hv : (1 : ℝ) ≤ v := by exact_mod_cast hW.trans_le hWv'
  have hVL : L ≤ (v : ℝ)*L^2 := by
    have hs : L ≤ L^2 := by nlinarith only [hL]
    exact hs.trans (le_mul_of_one_le_left (sq_nonneg L) hv)
  have hL0 : 0 ≤ L := by linarith only [hL]
  have hlogW : Real.log (1*W : ℕ) ≤ L-1 :=
    (Erdos972ExponentialSum.monotone_log_natCast (by simpa only [one_mul] using hWv'.trans hvN)).trans hLN
  have hlogWW : Real.log (W*W : ℕ) ≤ L-1 :=
    (Erdos972ExponentialSum.monotone_log_natCast (hWv.trans hvN)).trans hLN
  have hnlog (n : ℕ) (hn : n ∈ Ioc 0 N) : Real.log n ≤ L-1 :=
    (Erdos972ExponentialSum.monotone_log_natCast (mem_Ioc.mp hn).2).trans hLN
  have hglog (n : ℕ) (hn : n ∈ Ioc 0 N) : Real.log (floorMul α n) ≤ L-1 :=
    (Erdos972ExponentialSum.monotone_log_natCast
      ((floorMul_strictMono hα).monotone (mem_Ioc.mp hn).2)).trans hLg
  have hRc (n : ℕ) (hn : n ∈ Ioc 0 N) : |typeIIPart W W n| ≤ 4*(v : ℝ)*L^2 :=
    typeII_abs_of_log_bound hW hW hWv (mem_Ioc.mp hn).1 hL hlogWW (hnlog n hn)
  have hRo (n : ℕ) (hn : n ∈ Ioc 0 N) : |typeIIPart W W (floorMul α n)| ≤ 4*(v : ℝ)*L^2 :=
    typeII_abs_of_log_bound hW hW hWv (floorMul_pos hα (mem_Ioc.mp hn).1) hL hlogWW (hglog n hn)
  have hBc (n : ℕ) (hn : n ∈ Ioc 0 N) : |typeIPart 1 W n| ≤ 3*(v : ℝ)*L^2 :=
    typeIPart_abs_bound (by norm_num : 0 < 1) hW (by simpa only [one_mul] using hWv')
      (mem_Ioc.mp hn).1 hL hlogW (hnlog n hn)
  have hBo (n : ℕ) (hn : n ∈ Ioc 0 N) : |typeIPart 1 W (floorMul α n)| ≤ 3*(v : ℝ)*L^2 :=
    typeIPart_abs_bound (by norm_num : 0 < 1) hW (by simpa only [one_mul] using hWv')
      (floorMul_pos hα (mem_Ioc.mp hn).1) hL hlogW (hglog n hn)
  have hsoc (n : ℕ) (hn : n ∈ Ioc 0 N) : |cutoff vonMangoldt W (floorMul α n)| ≤ (v : ℝ)*L^2 := by
    rw [abs_of_nonneg (cutoff_vonMangoldt_nonneg _ _)]
    have hh := (cutoff_vonMangoldt_le W (floorMul α n)).trans
      (vonMangoldt_le_log.trans (hglog n hn))
    linarith only [hh, hVL]
  have hpsi : Chebyshev.psi W ≤ 7*(v : ℝ) :=
    (psi_le_seven_mul (Nat.cast_nonneg W)).trans
      (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hWv') (by norm_num))
  have hsc : total N (fun n => |cutoff vonMangoldt W n|) ≤ 7*(v : ℝ) := by
    simp only [abs_of_nonneg (cutoff_vonMangoldt_nonneg _ _), total]
    exact (cutoff_mangoldt_sum_le W N).trans hpsi
  have hso : total N (fun n => |cutoff vonMangoldt W (floorMul α n)|) ≤ 7*(v : ℝ) := by
    simp only [abs_of_nonneg (cutoff_vonMangoldt_nonneg _ _), total]
    exact (cutoff_mangoldt_output_sum_le hα W N).trans hpsi
  let F : ℕ → ℝ := fun n => typeIIPart W W n+reciprocalMoebius W*typeIPart 1 W n
  let G : ℕ → ℝ := fun n => typeIIPart W W (floorMul α n)+
    reciprocalMoebius W*typeIPart 1 W (floorMul α n)
  have hpert : |meanCenteredFourFactor α N W W W W-covariance N F G| ≤ 210*(v : ℝ)^2*L^2 := by
    have hh := recenter_small_cutoff_error hN (fun n => typeIIPart W W n)
      (fun n => typeIIPart W W (floorMul α n)) (fun n => typeIPart 1 W n)
      (fun n => typeIPart 1 W (floorMul α n)) (fun n => cutoff vonMangoldt W n)
      (fun n => cutoff vonMangoldt W (floorMul α n)) hm
      (by positivity : 0 ≤ 4*(v : ℝ)*L^2) (by positivity : 0 ≤ 3*(v : ℝ)*L^2)
      (by positivity : 0 ≤ (v : ℝ)*L^2) hRc hRo hBc hBo hsoc hsc hso
    have hid : meanCenteredFourFactor α N W W W W =
        covariance N
          (fun n => typeIIPart W W n+reciprocalMoebius W*(typeIPart 1 W n-cutoff vonMangoldt W n))
          (fun n => typeIIPart W W (floorMul α n)+reciprocalMoebius W*
            (typeIPart 1 W (floorMul α n)-cutoff vonMangoldt W (floorMul α n))) := by
      simp only [meanCenteredFourFactor, meanCenteredTypeII_eq, logTail_typeI,
        ArithmeticFunction.add_apply, pointScale_apply, sub_apply]
    rw [hid]
    dsimp only [F, G]
    convert hh using 1 <;> ring
  have hBR : |covariance N (fun n => typeIPart 1 W n)
      (fun n => typeIIPart W W (floorMul α n))| ≤ E₁+32*(N : ℝ)*|reciprocalMoebius W|+E := by
    simp_rw [typeII_eq_mangoldt_sub_typeI]
    rw [covariance_sub_right]
    exact (abs_sub _ _).trans (by linarith only [hleft, hBA])
  have hRB : |covariance N (fun n => typeIIPart W W n)
      (fun n => typeIPart 1 W (floorMul α n))| ≤ E₂+32*(N : ℝ)*|reciprocalMoebius W|+E := by
    simp_rw [typeII_eq_mangoldt_sub_typeI]
    rw [covariance_sub_left_recenter]
    exact (abs_sub _ _).trans (by linarith only [hright, hAB])
  have hmain := weighted_three_errors hm ((abs_nonneg _).trans hleft)
    ((abs_nonneg _).trans hright) hE hBR hRB hBB
  have hlin := (recenter_linear_error N (fun n => typeIIPart W W n)
    (fun n => typeIIPart W W (floorMul α n)) (fun n => typeIPart 1 W n)
    (fun n => typeIPart 1 W (floorMul α n)) (reciprocalMoebius W)).trans hmain
  change |covariance N F G-centeredFourFactor α N W W W W| ≤ _ at hlin
  have ht := (abs_sub_le (meanCenteredFourFactor α N W W W W) (covariance N F G)
    (centeredFourFactor α N W W W W)).trans (add_le_add hpert hlin)
  linarith only [ht]

#print axioms mean_recenter_covariance_bound
#print axioms recenter_small_cutoff_error
#print axioms recenter_linear_error
#print axioms weighted_three_errors
end Erdos972RecenterCovarianceBounds
