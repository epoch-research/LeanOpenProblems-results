import Submission.WideRankCellBudgetExplore

/-! Near-square-root width rank-cell windows and their aggregate insertion
budget. -/
namespace Erdos66NaturalScaleRankWindow
open Filter Erdos66Fractional Erdos66FractionalFourthPower Erdos66Generating
  Erdos66LogCellWindowBudget Erdos66RepairParameters Erdos66FlatProfileWindows
  Erdos66Rounding Erdos66CumulativeRoundingError
open scoped Topology
set_option maxHeartbeats 3500000

lemma profile_sqrt_log_upper (N : ℕ) (hN : 2 ≤ N) (hl : 1 ≤ Real.log (N : ℝ)) :
    Real.sqrt (N : ℝ)*profile N ≤ 2*Real.sqrt (Real.log N) := by
  have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hnp : (0 : ℝ)<N := by linarith
  have hH := harmonic_le_one_add_log (N+1)
  have hlog := Real.log_le_log (by positivity : (0 : ℝ)<(N : ℝ)+1)
    (show (N : ℝ)+1 ≤ (N : ℝ)^2 by nlinarith)
  rw [Real.log_pow] at hlog
  norm_num at hlog
  push_cast at hH
  have hp := profile_square_bound N
  have hs := Real.sq_sqrt hnp.le
  have hl0 : 0 ≤ Real.log (N : ℝ) := by linarith
  have hls := Real.sq_sqrt hl0
  have he : (Real.sqrt (N : ℝ)*profile N)^2=(N : ℝ)*(profile N)^2 := by rw [mul_pow,hs]
  push_cast at hp
  apply (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (profile_nonneg _)) (by positivity : 0 ≤ 2*Real.sqrt (Real.log N))).mp
  rw [he]
  have hb : (N : ℝ)*(profile N)^2 ≤ 3*Real.log N := by nlinarith [sq_nonneg (profile N)]
  nlinarith only [hb,hls,hl0]

noncomputable def densityWindow (N : ℕ) : ℕ := ⌈Real.sqrt (N : ℝ)/(16*Real.sqrt (Real.log N))⌉₊

lemma eventually_density_window : ∀ᶠ N : ℕ in atTop,
    0<densityWindow N ∧ densityWindow N ≤ N ∧ (densityWindow N : ℝ)*profile N ≤ 1/4 ∧
      Real.sqrt N/(16*Real.sqrt (Real.log N)) ≤ densityWindow N ∧
      (densityWindow N : ℝ) ≤ Real.sqrt N/(8*Real.sqrt (Real.log N)) := by
  have hlog : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 2,hlog.eventually_ge_atTop 1,
    (log_power_sqrt_decay 1).eventually_le_const (show (0 : ℝ)<1/16 by norm_num)]
    with N hN hl hdec
  have hn : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hsp := Real.sqrt_pos.mpr hn
  have hlp : 0<Real.log (N : ℝ) := by linarith
  simp only [pow_one] at hdec
  have hslog : Real.sqrt (Real.log (N : ℝ)) ≤ Real.log N :=
    Real.sqrt_le_iff.mpr ⟨hlp.le,by nlinarith⟩
  have hslog1 : 1 ≤ Real.sqrt (Real.log (N : ℝ)) := by
    simpa using Real.sqrt_le_sqrt hl
  have hslogpos : 0<Real.sqrt (Real.log (N : ℝ)) := by positivity
  have hsl : 16*Real.sqrt (Real.log (N : ℝ)) ≤ Real.sqrt N := by
    have hh := (div_le_iff₀ hsp).mp hdec
    linarith
  have hv1 : (1 : ℝ) ≤ Real.sqrt N/(16*Real.sqrt (Real.log N)) := (le_div_iff₀ (by positivity)).mpr (by simpa using hsl)
  have hlo : Real.sqrt N/(16*Real.sqrt (Real.log N)) ≤ densityWindow N := Nat.le_ceil _
  have hhi : (densityWindow N : ℝ) < Real.sqrt N/(16*Real.sqrt (Real.log N))+1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hwide : (densityWindow N : ℝ) ≤ Real.sqrt N/(8*Real.sqrt (Real.log N)) := by
    have he : Real.sqrt N/(8*Real.sqrt (Real.log N))=2*(Real.sqrt N/(16*Real.sqrt (Real.log N))) := by ring
    rw [he]
    linarith
  have hwpos : 0<densityWindow N := by exact_mod_cast (show (0 : ℝ)<densityWindow N by linarith)
  have hsqrt : Real.sqrt (N : ℝ) ≤ N := Real.sqrt_le_iff.mpr ⟨hn.le,by
    have hh : (2 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith⟩
  have hwN : densityWindow N ≤ N := by
    have hh : (densityWindow N : ℝ) ≤ N := hwide.trans ((div_le_self hsp.le (by linarith)).trans hsqrt)
    exact_mod_cast hh
  refine ⟨hwpos,hwN,?_,hlo,hwide⟩
  have hp := profile_sqrt_log_upper N hN hl
  have hh := mul_le_mul_of_nonneg_right hwide (profile_nonneg N)
  have he : Real.sqrt (N : ℝ)/(8*Real.sqrt (Real.log N))*profile N ≤ 1/4 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : 0<8*Real.sqrt (Real.log (N : ℝ)))).mpr
    linarith
  exact hh.trans he

lemma normalized_interval_mass_bound (N m w : ℕ) (hN : 3 ≤ N) (hl : 1 ≤ Real.log (N : ℝ))
    (hm : m ≤ N) (hw : 0<w) (hwN : w ≤ N) :
    (∑ i∈Finset.range (m*w), profile i)/((w : ℝ)*Real.log N) ≤
      Real.sqrt (12*((m : ℝ)+1)/((w : ℝ)*Real.log N)) := by
  have hlp : 0<Real.log (N : ℝ) := by linarith
  have hwp : (0 : ℝ)<w := by exact_mod_cast hw
  have hh := Erdos66WideRankCellBudget.interval_mass_ratio_bound N m w hN hl hm hw hwN
  calc
    _ = ((∑ i∈Finset.range (m*w), profile i)/(w : ℝ))/Real.log N := (div_div _ _ _).symm
    _ ≤ Real.sqrt (12*((m : ℝ)+1)*Real.log N/w)/Real.log N := div_le_div_of_nonneg_right hh hlp.le
    _ = Real.sqrt ((12*((m : ℝ)+1)*Real.log N/w)/(Real.log N)^2) := by
      conv_rhs => rw [Real.sqrt_div (by positivity),Real.sqrt_sq hlp.le]
    _ = _ := by congr 1; field_simp

lemma count_scale_atTop : Tendsto (fun N : ℕ ↦ Real.sqrt ((N : ℝ)*Real.log N)) atTop atTop :=
  Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.atTop_mul_atTop₀
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))

lemma inverse_count_scale_decay :
    Tendsto (fun N : ℕ ↦ 1/Real.sqrt ((N : ℝ)*Real.log N)) atTop (𝓝 0) := by
  simpa only [one_div] using count_scale_atTop.inv_tendsto_atTop

end Erdos66NaturalScaleRankWindow
