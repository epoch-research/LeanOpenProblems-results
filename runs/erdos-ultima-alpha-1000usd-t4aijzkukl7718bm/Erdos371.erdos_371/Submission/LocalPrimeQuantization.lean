import Submission.PrimeLogQuantization

/-! Fixed local prime-log labels and the finite quantizer's discontinuities. -/
namespace Erdos371
open Finset Filter
open scoped Topology
set_option autoImplicit false

noncomputable def localPrimeRatio (n : ℕ) : ℝ := normalizedPrimeLog n n
noncomputable def localPrimeLabel (Q n : ℕ) : Fin (Q+1) := unitQuantize Q (localPrimeRatio n)

lemma localPrimeRatio_mem_unit (n : ℕ) : 0 ≤ localPrimeRatio n ∧ localPrimeRatio n ≤ 1 := by
  rcases le_or_gt n 1 with hn | hn
  · interval_cases n <;> norm_num [localPrimeRatio,normalizedPrimeLog,primeLog]
  · exact normalizedPrimeLog_mem_unit n n hn le_rfl

/-- A quantization change must cross one of the finitely many positive
thresholds. The distance is measured at the original point x. -/
lemma unitQuantize_boundary_of_ne (Q : ℕ) (hQ : 0 < Q) (x y : ℝ)
    (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1)
    (hne : unitQuantize Q x ≠ unitQuantize Q y) :
    ∃ j ∈ Icc 1 Q, |x-(j : ℝ)/Q| ≤ |x-y| := by
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hex := unitQuantize_error Q hQ x hx.1 hx.2
  have hey := unitQuantize_error Q hQ y hy.1 hy.2
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · let j := (unitQuantize Q y).val
    have hv : (unitQuantize Q x).val+1 ≤ j := by exact hlt
    have hj : j ∈ Icc 1 Q := mem_Icc.mpr ⟨by omega,by have := (unitQuantize Q y).isLt; omega⟩
    have hvR : ((unitQuantize Q x).val : ℝ)+1 ≤ j := by exact_mod_cast hv
    have hdiv := div_le_div_of_nonneg_right hvR hQr.le
    rw [add_div] at hdiv
    have hxj : x < (j : ℝ)/Q := by linarith
    have hjy : (j : ℝ)/Q ≤ y := by dsimp [j]; linarith
    refine ⟨j,hj,?_⟩
    rw [abs_of_neg (sub_neg.mpr hxj),abs_of_neg (sub_neg.mpr (hxj.trans_le hjy))]
    linarith
  · let j := (unitQuantize Q x).val
    have hv : (unitQuantize Q y).val+1 ≤ j := by exact hlt
    have hj : j ∈ Icc 1 Q := mem_Icc.mpr ⟨by omega,by have := (unitQuantize Q x).isLt; omega⟩
    have hvR : ((unitQuantize Q y).val : ℝ)+1 ≤ j := by exact_mod_cast hv
    have hdiv := div_le_div_of_nonneg_right hvR hQr.le
    rw [add_div] at hdiv
    have hyj : y < (j : ℝ)/Q := by linarith
    have hjx : (j : ℝ)/Q ≤ x := by dsimp [j]; linarith
    refine ⟨j,hj,?_⟩
    rw [abs_of_nonneg (sub_nonneg.mpr hjx),abs_of_pos (sub_pos.mpr (hyj.trans_le hjx))]
    linarith

lemma localPrimeRatio_mul_bound (k n : ℕ) (hk : 0 < k) (hn : 1 < n) :
    |localPrimeRatio (k*n)-localPrimeRatio n| ≤ Real.log k/Real.log n := by
  have hkR : (0 : ℝ)<k := by exact_mod_cast hk
  have hnR : (0 : ℝ)<n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hl : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hb : 0 ≤ Real.log (k : ℝ) := Real.log_natCast_nonneg k
  have hL : 0 < Real.log (k : ℝ)+Real.log n := by linarith
  have hnum := primeLog_mul_change k n hk
  have hA := primeLog_nonneg n
  have hAup := primeLog_le_log n
  have hAprime := primeLog_nonneg (k*n)
  unfold localPrimeRatio normalizedPrimeLog
  rw [Nat.cast_mul,Real.log_mul hkR.ne' hnR.ne',abs_le]
  constructor
  · have hlow : (primeLog n-Real.log k)/Real.log n ≤
        primeLog (k*n)/(Real.log k+Real.log n) := by
      apply (div_le_div_iff₀ hl hL).mpr
      nlinarith [sq_nonneg (Real.log (k : ℝ))]
    rw [sub_div] at hlow
    linarith
  · have hup : primeLog (k*n)/(Real.log k+Real.log n) ≤
        (primeLog n+Real.log k)/Real.log n := by
      apply (div_le_div_iff₀ hL hl).mpr
      nlinarith [sq_nonneg (Real.log (k : ℝ))]
    rw [add_div] at hup
    linarith

lemma localPrimeRatio_mul_tendsto (k : ℕ) (hk : 0 < k) :
    Tendsto (fun n : ℕ => localPrimeRatio (k*n)-localPrimeRatio n) atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => Real.log k/Real.log n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  apply squeeze_zero_norm' _ ht
  filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
  simpa only [Real.norm_eq_abs] using localPrimeRatio_mul_bound k n hk hn

#print axioms unitQuantize_boundary_of_ne
#print axioms localPrimeRatio_mul_tendsto
end Erdos371
