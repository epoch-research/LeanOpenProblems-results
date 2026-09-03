import Submission.LogCellWindowBudgetExplore
import Submission.BracketWindowOccupancyExplore

/-! Near-square-root width rank-cell windows and their aggregate insertion
budget. -/
namespace Erdos66WideRankCellBudget
open Filter Erdos66Fractional Erdos66FractionalFourthPower Erdos66Generating
  Erdos66LogCellWindowBudget Erdos66RepairParameters Erdos66FlatProfileWindows
  Erdos66Rounding Erdos66CumulativeRoundingError
open scoped Topology
set_option maxHeartbeats 3500000

noncomputable def wideWindow (N : ℕ) : ℕ := ⌈Real.sqrt (N : ℝ)/(16*Real.log N)⌉₊

lemma eventually_wide_window : ∀ᶠ N : ℕ in atTop,
    0<wideWindow N ∧ wideWindow N ≤ N ∧ (wideWindow N : ℝ)*profile N ≤ 1/4 ∧
      Real.sqrt N/(16*Real.log N) ≤ wideWindow N ∧
      (wideWindow N : ℝ) ≤ Real.sqrt N/(8*Real.log N) := by
  have hlog : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 2,hlog.eventually_ge_atTop 1,
    (log_power_sqrt_decay 1).eventually_le_const (show (0 : ℝ)<1/16 by norm_num)]
    with N hN hl hdec
  have hn : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hsp := Real.sqrt_pos.mpr hn
  have hlp : 0<Real.log (N : ℝ) := by linarith
  simp only [pow_one] at hdec
  have hsl : 16*Real.log (N : ℝ) ≤ Real.sqrt N := by
    have hh := (div_le_iff₀ hsp).mp hdec
    linarith
  have hv1 : (1 : ℝ) ≤ Real.sqrt N/(16*Real.log N) := (le_div_iff₀ (by positivity)).mpr (by simpa using hsl)
  have hlo : Real.sqrt N/(16*Real.log N) ≤ wideWindow N := Nat.le_ceil _
  have hhi : (wideWindow N : ℝ) < Real.sqrt N/(16*Real.log N)+1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hwide : (wideWindow N : ℝ) ≤ Real.sqrt N/(8*Real.log N) := by
    have he : Real.sqrt N/(8*Real.log N)=2*(Real.sqrt N/(16*Real.log N)) := by ring
    rw [he]
    linarith
  have hwpos : 0<wideWindow N := by exact_mod_cast (show (0 : ℝ)<wideWindow N by linarith)
  have hsqrt : Real.sqrt (N : ℝ) ≤ N := Real.sqrt_le_iff.mpr ⟨hn.le,by
    have hh : (2 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith⟩
  have hwN : wideWindow N ≤ N := by
    have hh : (wideWindow N : ℝ) ≤ N := hwide.trans ((div_le_self hsp.le (by linarith)).trans hsqrt)
    exact_mod_cast hh
  refine ⟨hwpos,hwN,?_,hlo,hwide⟩
  have hp := profile_sqrt_upper N hN hl
  have hh := mul_le_mul_of_nonneg_right hwide (profile_nonneg N)
  have he : Real.sqrt (N : ℝ)/(8*Real.log N)*profile N ≤ 1/4 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : 0<8*Real.log (N : ℝ))).mpr
    linarith
  exact hh.trans he

lemma interval_mass_ratio_bound (N m w : ℕ) (hN : 3 ≤ N) (hl : 1 ≤ Real.log (N : ℝ))
    (hm : m ≤ N) (hw : 0<w) (hwN : w ≤ N) :
    (∑ i∈Finset.range (m*w), profile i)/(w : ℝ) ≤
      Real.sqrt (12*((m : ℝ)+1)*Real.log N/w) := by
  have hn : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hwR : (1 : ℝ) ≤ w := by exact_mod_cast hw
  have hwp : (0 : ℝ)<w := by linarith
  have hmw : (m : ℝ)*w ≤ (N : ℝ)^2 := by
    have hh := Nat.mul_le_mul hm hwN
    simpa only [pow_two] using (show (m : ℝ)*w ≤ (N : ℝ)*N by exact_mod_cast hh)
  have hH := harmonic_le_one_add_log (2*(m*w)+1)
  push_cast at hH
  have hlog := Real.log_le_log (by positivity : (0 : ℝ)<2*((m : ℝ)*w)+1)
    (show 2*((m : ℝ)*w)+1 ≤ (N : ℝ)^3 by nlinarith [sq_nonneg ((N : ℝ)-3)])
  rw [Real.log_pow] at hlog
  norm_num at hlog
  have hH' : (harmonic (2*(m*w)+1) : ℝ) ≤ 4*Real.log N := by linarith
  have hc : ((2*(m*w)+1 : ℕ) : ℝ) ≤ 3*((m : ℝ)+1)*w := by
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  have hP := (profile_prefix_square_bound (m*w)).trans
    (mul_le_mul hc hH' (harmonic_nonneg _) (by positivity : 0 ≤ 3*((m : ℝ)+1)*w))
  have hs : (∑ i∈Finset.range (m*w), profile i) ≤ prefixSum profile (m*w) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (fun i _ _ ↦ profile_nonneg i)
  have hs0 : 0 ≤ ∑ i∈Finset.range (m*w), profile i := Finset.sum_nonneg (fun i _ ↦ profile_nonneg i)
  have hs2 := sq_le_sq₀ hs0 (prefix_nonneg (m*w)) |>.mpr hs
  apply Real.le_sqrt_of_sq_le
  rw [div_pow]
  apply (div_le_iff₀ (sq_pos_of_pos hwp)).mpr
  have he : 12*((m : ℝ)+1)*Real.log N/(w : ℝ)*(w : ℝ)^2 =
      12*((m : ℝ)+1)*w*Real.log N := by field_simp
  rw [he]
  nlinarith only [hs2,hP]

end Erdos66WideRankCellBudget
