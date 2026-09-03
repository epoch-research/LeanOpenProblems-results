import Submission.DualTypeICovariance

/-! True covariance on the original Type-I side, rather than centering at
an approximate Chebyshev mean. -/
namespace Erdos972OriginalTypeICovariance

open Finset ArithmeticFunction
open Erdos972LogarithmicCovariance Erdos972TypeICovariance Erdos972TypeIPolynomial
open Erdos972LogDivisorProfiles Erdos972Vaughan Erdos972DoubleVaughan
open Erdos972PrimePowerError Erdos972ChebyshevRowMean Erdos972CenteredVaughan
open Erdos972CorrelationVaughan Erdos972GrowingTypeI Erdos972MovingCenteredRows
open Erdos972WeightedBeattyRows Erdos972RealLogCenter

set_option maxHeartbeats 1000000

lemma covariance_center_identity {N : ℕ} (hN : 0 < N) (f g : ℕ → ℝ) (ρ : ℝ) :
    covariance N f g = total N (fun n => f n*(g n-ρ))-
      (total N f/N)*(total N g-ρ*N) := by
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  simp only [covariance, total, mul_sub, sum_sub_distrib, ← sum_mul]
  field_simp
  ring

lemma typeIPart_centered_sum (α ρ : ℝ) (U V N : ℕ) :
    total N (fun n => typeIPart U V n*(vonMangoldt (floorMul α n)-ρ)) =
      first α ρ U N-second α ρ U V N+small α ρ V N := by
  change weightedSum (typeIPart U V) (centeredOutput α ρ) N = _
  rw [typeIPart, weightedSum_add, weightedSum_sub, first_eq, second_eq]
  rfl

lemma typeIPart_abs_bound {U V v n : ℕ} (hU : 0 < U) (hV : 0 < V)
    (hUv : U*V ≤ v) (hn : 0 < n) {L : ℝ} (hL : 1 ≤ L)
    (hlogD : Real.log (U*V : ℕ) ≤ L-1) (hlogn : Real.log n ≤ L-1) :
    |typeIPart U V n| ≤ 3*(v : ℝ)*L^2 := by
  have hvR : (1 : ℝ) ≤ v := by exact_mod_cast (Nat.mul_pos hU hV).trans_le hUv
  have hM := typeI_profileMass_le hUv hL hlogD
  have hb := (profile_abs_of_log_le (U*V) (slopeCoeff U) (constantCoeff U V) n hL hlogn).trans
    (mul_le_mul_of_nonneg_left hM (by linarith : 0 ≤ L))
  rw [typeIPart_profile U V hV hn]
  apply (abs_add_le _ _).trans
  rw [abs_of_nonneg (cutoff_vonMangoldt_nonneg _ _)]
  have hc := (cutoff_vonMangoldt_le V n).trans (vonMangoldt_le_log.trans hlogn)
  have hL2 : L ≤ (v : ℝ)*L^2 := by
    have hh : L ≤ L^2 := by nlinarith only [hL]
    exact hh.trans (le_mul_of_one_le_left (sq_nonneg L) hvR)
  nlinarith only [hb, hc, hL2]

/-- The correction from the approximate mean to true covariance has the
same quantitative small-row error and only a further logarithmic loss. -/
theorem original_typeI_covariance_bound {α E : ℝ} (hα : 1 < α) (hI : Irrational α) (hE : 0 ≤ E)
    {N U V v : ℕ} (hU : 0 < U) (hV : 0 < V) (hUV : U*V ≤ v) (hvN : v ≤ N)
    (hrows : ∀ m : ℕ, 0 < m → m ≤ v → ∀ X ≤ floorMul (α*m) (N/m),
      |outputRow (α*m) (fun q => vonMangoldt q) X-(1/(α*m))*Chebyshev.psi X| ≤ E) :
    |covariance N (fun n => typeIPart U V n) (fun n => vonMangoldt (floorMul α n))| ≤
      200*(v : ℝ)*(1+Real.log (α*N))^3*(E+1)+2*|commonLogCenter (α*N)|/α := by
  have hv : 0 < v := (Nat.mul_pos hU hV).trans_le hUV
  have hN : 0 < N := hv.trans_le hvN
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hα0 : 0 < α := by linarith
  have hαN : (N : ℝ) ≤ α*N := le_mul_of_one_le_left hNR.le hα.le
  have hy : 1 ≤ α*N := (by exact_mod_cast hN : (1 : ℝ) ≤ N).trans hαN
  let L : ℝ := 1+Real.log (α*N)
  have hL : 1 ≤ L := by dsimp only [L]; linarith [Real.log_nonneg hy]
  have hlogN : Real.log N ≤ L-1 := by
    dsimp only [L]
    linarith only [Real.log_le_log hNR hαN]
  have hlogD : Real.log (U*V : ℕ) ≤ L-1 :=
    (Erdos972ExponentialSum.monotone_log_natCast (hUV.trans hvN)).trans hlogN
  have hUv : U ≤ v := (show U ≤ U*V by nlinarith).trans hUV
  have hVv : V ≤ v := (show V ≤ U*V by nlinarith).trans hUV
  have htype := typeI_uniform_budget hα hI hE hN hvN hUv hVv hUV hrows
  have hcenter : |total N (fun n => typeIPart U V n*(vonMangoldt (floorMul α n)-commonMean α N))| ≤
      100*(v : ℝ)*L^2*(E+1)+2*|commonLogCenter (α*N)|/α := by
    rw [typeIPart_centered_sum]
    exact ((abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)).trans htype
  have hrow : |total N (fun n => vonMangoldt (floorMul α n))-commonMean α N*N| ≤ E+2*L+5 := by
    have hh := common_centered_row hα hI hy N le_rfl (by nlinarith only [hα0])
      (by simpa only [Nat.cast_one, mul_one, Nat.div_one] using hrows 1 (by norm_num) hv _ le_rfl)
    have he : (∑ n ∈ Ioc 0 N, (vonMangoldt (floorMul α n)-Chebyshev.psi (α*N)/(α*N))) =
        total N (fun n => vonMangoldt (floorMul α n))-commonMean α N*N := by
      simp only [total, commonMean, sum_sub_distrib, sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul]
      ring
    rw [he] at hh
    dsimp only [L]
    linarith only [hh]
  have hmean : |total N (fun n => typeIPart U V n)/N| ≤ 3*(v : ℝ)*L^2 := by
    rw [abs_div, abs_of_nonneg hNR.le]
    apply (div_le_iff₀ hNR).mpr
    have hh := total_abs_le (fun n hn => typeIPart_abs_bound hU hV hUV (mem_Ioc.mp hn).1 hL hlogD
      ((log_input_le hn).trans hlogN))
    exact hh.trans_eq (by ring)
  rw [covariance_center_identity hN _ _ (commonMean α N)]
  apply (abs_sub _ _).trans
  rw [abs_mul]
  have hcor := mul_le_mul hmean hrow (abs_nonneg _) (by positivity)
  have hpoly : 100*(E+1)+3*(E+2*L+5) ≤ 200*L*(E+1) := by
    nlinarith only [hL, hE, mul_nonneg (show 0 ≤ L-1 by linarith only [hL]) hE]
  have hb := mul_le_mul_of_nonneg_left hpoly (show 0 ≤ (v : ℝ)*L^2 by positivity)
  change _ ≤ 200*(v : ℝ)*L^3*(E+1)+2*|commonLogCenter (α*N)|/α
  nlinarith only [hcenter, hcor, hb]

#print axioms original_typeI_covariance_bound

end Erdos972OriginalTypeICovariance
