import Submission.WeightedBeattyRows

/-! A real common endpoint for logarithmically weighted prime-output rows. -/
namespace Erdos972RealLogCenter

open Finset Filter ArithmeticFunction
open scoped Topology
open Erdos972SelfCenteredLog Erdos972CommonLogCenter Erdos972ChebyshevRowMean

set_option maxHeartbeats 1000000

noncomputable def commonLogCenter (y : ℝ) : ℝ :=
  logRow (fun q => vonMangoldt q) ⌊y⌋₊-(Real.log y-1)*Chebyshev.psi y

lemma psi_floor (y : ℝ) : Chebyshev.psi (⌊y⌋₊ : ℕ) = Chebyshev.psi y := by
  simp only [Chebyshev.psi, Nat.floor_natCast]

lemma log_floor_gap {y : ℝ} (hy : 1 ≤ y) :
    0 ≤ Real.log y-Real.log (⌊y⌋₊ : ℕ) ∧
      (Real.log y-Real.log (⌊y⌋₊ : ℕ))*(⌊y⌋₊ : ℕ) ≤ 1 := by
  have hy0 : 0 < y := by linarith
  have hP : 0 < ⌊y⌋₊ := Nat.floor_pos.mpr hy
  have hP0 : (0 : ℝ) < (⌊y⌋₊ : ℕ) := Nat.cast_pos.mpr hP
  have hlo := Nat.floor_le hy0.le
  refine ⟨sub_nonneg.mpr (Real.log_le_log hP0 hlo), ?_⟩
  have hh := Real.log_le_sub_one_of_pos (div_pos hy0 hP0)
  rw [Real.log_div hy0.ne' hP0.ne'] at hh
  have hm := mul_le_mul_of_nonneg_right hh hP0.le
  have he : (y/(⌊y⌋₊ : ℕ)-1)*(⌊y⌋₊ : ℕ) = y-(⌊y⌋₊ : ℕ) := by field_simp
  rw [he] at hm
  linarith [Nat.lt_floor_add_one y]

lemma commonLogCenter_floor_error {y : ℝ} (hy : 1 ≤ y) :
    |commonLogCenter y-commonLogCenterNat ⌊y⌋₊| ≤ 7 := by
  have hg := log_floor_gap hy
  have he : commonLogCenter y-commonLogCenterNat ⌊y⌋₊ =
      -(Real.log y-Real.log (⌊y⌋₊ : ℕ))*Chebyshev.psi (⌊y⌋₊ : ℕ) := by
    unfold commonLogCenter commonLogCenterNat
    rw [psi_floor]
    ring
  rw [he, abs_mul, abs_neg, abs_of_nonneg hg.1, abs_of_nonneg (Chebyshev.psi_nonneg _)]
  calc
    _ ≤ (Real.log y-Real.log (⌊y⌋₊ : ℕ))*(7*(⌊y⌋₊ : ℕ)) :=
      mul_le_mul_of_nonneg_left (psi_le_seven_mul (Nat.cast_nonneg _)) hg.1
    _ ≤ 7 := by nlinarith only [hg.2]

/-- Only qualitative PNT is needed for this common scalar. -/
theorem commonLogCenter_div_tendsto :
    Tendsto (fun y : ℝ => commonLogCenter y/y) atTop (𝓝 0) := by
  have hf : Tendsto (fun y : ℝ => ⌊y⌋₊) atTop atTop := tendsto_nat_floor_atTop
  have hn : Tendsto (fun y : ℝ => |commonLogCenterNat ⌊y⌋₊/(⌊y⌋₊ : ℕ)|) atTop (𝓝 0) := by
    simpa only [abs_zero] using (commonLogCenterNat_div_tendsto.comp hf).abs
  have hh := hn.add (show Tendsto (fun y : ℝ => 7/y) atTop (𝓝 0) from tendsto_const_nhds.div_atTop tendsto_id)
  simp only [add_zero] at hh
  apply squeeze_zero_norm' _ hh
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
  have hy0 : 0 < y := by linarith
  have hP0 : (0 : ℝ) < (⌊y⌋₊ : ℕ) := Nat.cast_pos.mpr (Nat.floor_pos.mpr hy)
  rw [Real.norm_eq_abs, abs_div, abs_of_nonneg hy0.le, abs_div, abs_of_nonneg hP0.le]
  calc
    _ ≤ (|commonLogCenterNat ⌊y⌋₊|+7)/y := by
      apply div_le_div_of_nonneg_right _ hy0.le
      have hb := abs_sub_le (commonLogCenter y) (commonLogCenterNat ⌊y⌋₊) 0
      simp only [sub_zero] at hb
      linarith only [hb, commonLogCenter_floor_error hy]
    _ ≤ _ := by
      rw [add_div]
      exact add_le_add (div_le_div_of_nonneg_left (abs_nonneg _) hP0 (Nat.floor_le hy0.le)) le_rfl

lemma output_endpoint_bound {x y c : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : 1 ≤ y)
    (hc0 : 0 ≤ c) (hc : c ≤ Real.log y) :
    |(logRow (fun q => vonMangoldt q) ⌊y⌋₊-c*Chebyshev.psi y)-
      (logRow (fun q => vonMangoldt q) ⌊x⌋₊-c*Chebyshev.psi x)| ≤
        (y-x+1)*(Real.log y)^2 := by
  have hf : ⌊x⌋₊ ≤ ⌊y⌋₊ := Nat.floor_mono hxy
  have he : (logRow (fun q => vonMangoldt q) ⌊y⌋₊-c*Chebyshev.psi y)-
      (logRow (fun q => vonMangoldt q) ⌊x⌋₊-c*Chebyshev.psi x) =
      ∑ q ∈ Ioc ⌊x⌋₊ ⌊y⌋₊, (Real.log q-c)*vonMangoldt q := by
    have hh := sum_Ioc_consecutive (fun q => (Real.log q-c)*vonMangoldt q) (Nat.zero_le ⌊x⌋₊) hf
    simp only [sub_mul, sum_sub_distrib, ← mul_sum] at hh
    unfold logRow Chebyshev.psi
    simp only [sub_mul, sum_sub_distrib, ← mul_sum]
    linarith only [hh]
  have hcard : ((Ioc ⌊x⌋₊ ⌊y⌋₊).card : ℝ) ≤ y-x+1 := by
    rw [Nat.card_Ioc, Nat.cast_sub hf]
    linarith [Nat.floor_le (hx.trans hxy), Nat.lt_floor_add_one x]
  rw [he]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ q ∈ Ioc ⌊x⌋₊ ⌊y⌋₊, (Real.log y)^2 := by
      apply sum_le_sum
      intro q hq
      have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (Nat.zero_lt_of_lt (mem_Ioc.mp hq).1)
      have hqlog : Real.log q ≤ Real.log y := Real.log_le_log hq0
        ((Nat.cast_le.mpr (mem_Ioc.mp hq).2).trans (Nat.floor_le (hx.trans hxy)))
      have hdiff : |Real.log q-c| ≤ Real.log y := abs_le.mpr ⟨by linarith [Real.log_natCast_nonneg q], by linarith⟩
      rw [abs_mul, abs_of_nonneg vonMangoldt_nonneg]
      exact (mul_le_mul hdiff (vonMangoldt_le_log.trans hqlog) vonMangoldt_nonneg (Real.log_nonneg hy)).trans_eq (by ring)
    _ = ((Ioc ⌊x⌋₊ ⌊y⌋₊).card : ℝ)*(Real.log y)^2 := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (sq_nonneg _)

lemma logMass_interpolation {L : ℕ} (hL : 0 < L) {t y : ℝ}
    (hLt : (L : ℝ) ≤ t) (htL : t ≤ (L : ℝ)+1) (hty : t ≤ y) :
    |logMass L-(t*Real.log t-t)| ≤ 3+2*Real.log y := by
  have hLR : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (0 : ℝ) < L := Nat.cast_pos.mpr hL
  have ht0 : 0 < t := hL0.trans_le hLt
  have hly : Real.log L ≤ Real.log y := Real.log_le_log hL0 (hLt.trans hty)
  have htylog : Real.log t ≤ Real.log y := Real.log_le_log ht0 hty
  have hlogt0 : 0 ≤ Real.log t := Real.log_nonneg (hLR.trans hLt)
  have hdelta : 0 ≤ Real.log t-Real.log L := sub_nonneg.mpr (Real.log_le_log hL0 hLt)
  have hdelta1 : (L : ℝ)*(Real.log t-Real.log L) ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (div_pos ht0 hL0)
    rw [Real.log_div ht0.ne' hL0.ne'] at hh
    have hm := mul_le_mul_of_nonneg_left hh hL0.le
    have he : (L : ℝ)*(t/L-1) = t-L := by field_simp
    rw [he] at hm
    linarith only [hm, htL]
  have he : (t*Real.log t-t)-((L : ℝ)*Real.log L-L) =
      (t-L)*(Real.log t-1)+(L : ℝ)*(Real.log t-Real.log L) := by ring
  have hinter : |(t*Real.log t-t)-((L : ℝ)*Real.log L-L)| ≤ Real.log t+2 := by
    rw [he]
    apply (abs_add_le _ _).trans
    rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr hLt), abs_of_nonneg (mul_nonneg hL0.le hdelta)]
    have hlog : |Real.log t-1| ≤ Real.log t+1 := by simpa only [abs_of_nonneg hlogt0, abs_one] using abs_sub (Real.log t) 1
    have hm : (t-L)*|Real.log t-1| ≤ Real.log t+1 := by
      calc
        _ ≤ 1*(Real.log t+1) := mul_le_mul (by linarith only [htL]) hlog (abs_nonneg _) (by norm_num)
        _ = _ := one_mul _
    linarith only [hm, hdelta1]
  have hmass := logMass_error_bounds hL
  have habs : |logMass L-((L : ℝ)*Real.log L-L)| ≤ 1+Real.log L := by
    rw [abs_of_nonneg hmass.1]
    exact hmass.2
  have hh := abs_sub_le (logMass L) ((L : ℝ)*Real.log L-L) (t*Real.log t-t)
  rw [abs_sub_comm ((L : ℝ)*Real.log L-L)] at hh
  linarith only [hh, habs, hinter, hly, htylog]

/-- Aligning a row at a common real endpoint costs only a squared logarithm,
uniformly in the row multiplier. -/
theorem log_main_endpoint_bound {β y : ℝ} (hβ : 1 ≤ β) {L : ℕ} (hL : 0 < L)
    (hlo : β*L ≤ y) (hhi : y ≤ β*((L : ℝ)+1)) :
    |(1/β)*(logRow (fun q => vonMangoldt q) ⌊β*L⌋₊-Real.log β*Chebyshev.psi (β*L))-
      (Chebyshev.psi y/y)*logMass L-commonLogCenter y/β| ≤ 24*(1+Real.log y)^2 := by
  have hLR : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hβ0 : 0 < β := by linarith
  have hβy : β ≤ y := (le_mul_of_one_le_right hβ0.le hLR).trans hlo
  have hy : 1 ≤ y := hβ.trans hβy
  have hy0 : 0 < y := by linarith
  have hlog : 0 ≤ Real.log y := Real.log_nonneg hy
  have hlogβ : Real.log β ≤ Real.log y := Real.log_le_log hβ0 hβy
  let t := y/β
  have hLt : (L : ℝ) ≤ t := (le_div_iff₀ hβ0).mpr (by nlinarith only [hlo])
  have htL : t ≤ (L : ℝ)+1 := (div_le_iff₀ hβ0).mpr (by nlinarith only [hhi])
  have hty : t ≤ y := div_le_self hy0.le hβ
  have hmass := logMass_interpolation hL hLt htL hty
  have hend := output_endpoint_bound (show 0 ≤ β*L by positivity) hlo hy (Real.log_nonneg hβ) hlogβ
  have hend' : |(logRow (fun q => vonMangoldt q) ⌊y⌋₊-Real.log β*Chebyshev.psi y)-
      (logRow (fun q => vonMangoldt q) ⌊β*L⌋₊-Real.log β*Chebyshev.psi (β*L))|/β ≤ 2*(Real.log y)^2 := by
    apply (div_le_iff₀ hβ0).mpr
    apply hend.trans
    have hh : y-β*L+1 ≤ 2*β := by nlinarith only [hhi, hβ]
    nlinarith only [mul_le_mul_of_nonneg_right hh (sq_nonneg (Real.log y))]
  have hρ := psi_ratio_bounds hy0
  have hlogt : Real.log t = Real.log y-Real.log β := Real.log_div hy0.ne' hβ0.ne'
  have he : (1/β)*(logRow (fun q => vonMangoldt q) ⌊β*L⌋₊-Real.log β*Chebyshev.psi (β*L))-
      (Chebyshev.psi y/y)*logMass L-commonLogCenter y/β =
      -((logRow (fun q => vonMangoldt q) ⌊y⌋₊-Real.log β*Chebyshev.psi y)-
        (logRow (fun q => vonMangoldt q) ⌊β*L⌋₊-Real.log β*Chebyshev.psi (β*L)))/β+
        (Chebyshev.psi y/y)*((t*Real.log t-t)-logMass L) := by
    rw [hlogt]
    unfold commonLogCenter
    dsimp only [t]
    field_simp
    ring
  rw [he]
  apply (abs_add_le _ _).trans
  rw [abs_div, abs_neg, abs_of_nonneg hβ0.le, abs_mul, abs_of_nonneg hρ.1, abs_sub_comm (t*Real.log t-t)]
  have hm : (Chebyshev.psi y/y)*|logMass L-(t*Real.log t-t)| ≤ 7*(3+2*Real.log y) :=
    mul_le_mul hρ.2 hmass (abs_nonneg _) (by norm_num)
  nlinarith only [hend', hm, hlog, sq_nonneg (Real.log y)]

#print axioms commonLogCenter_div_tendsto
#print axioms log_main_endpoint_bound

end Erdos972RealLogCenter
