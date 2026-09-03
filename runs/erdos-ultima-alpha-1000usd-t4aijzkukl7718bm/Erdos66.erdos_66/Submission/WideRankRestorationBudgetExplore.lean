import Submission.WideRankCellBudgetExplore

/-! The aggregate restoration potential is feasible at every fixed power
strictly below the square-root demand scale. -/
namespace Erdos66WideRankRestorationBudget
open Filter Erdos66Fractional Erdos66WideRankCellBudget Erdos66LogCellWindowBudget
  Erdos66RepairParameters
open scoped Topology
set_option maxHeartbeats 4500000

lemma augmented_demand_decay (S : ℕ → ℝ)
    (hdec : Tendsto (fun N : ℕ ↦ S N*(Real.log N)^2/Real.sqrt N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ ↦ (S N+1)*(Real.log N)^2/Real.sqrt N) atTop (𝓝 0) := by
  have hh := hdec.add (log_power_sqrt_decay 2)
  simp only [add_zero] at hh
  convert hh using 1
  ext N
  ring

/-- The demand hypothesis is stronger than necessary for a logarithmic load,
but makes the entire insertion mean tend to zero. -/
theorem eventually_wide_rank_budget (S : ℕ → ℝ) (hS : ∀ᶠ N in atTop, 0 ≤ S N)
    (hdec : Tendsto (fun N : ℕ ↦ S N*(Real.log N)^2/Real.sqrt N) atTop (𝓝 0))
    (ε : ℝ) (hε : 0<ε) (h : ℕ) :
    let t : ℝ := 20*((h : ℝ)+1)/ε
    0<t ∧ ∀ᶠ N : ℕ in atTop, ∀ m : ℕ, (m : ℝ) ≤ S N →
      (wideWindow N : ℝ)/2+3 ≤ wideWindow N ∧
      ((N : ℝ)^h+1)*Real.exp
        (Real.exp t*((∑ i∈Finset.range (m*wideWindow N), profile i)+5*m)/((wideWindow N : ℝ)/2)-
          t*(ε*Real.log N/10))<1 := by
  dsimp only
  let t : ℝ := 20*((h : ℝ)+1)/ε
  let δ (N : ℕ) := (S N+1)*(Real.log N)^2/Real.sqrt N
  let E (N : ℕ) := 2*Real.exp t*(Real.sqrt (192*δ N)+80*δ N)
  have ht : 0<t := by dsimp [t]; positivity
  have hδ : Tendsto δ atTop (𝓝 0) := augmented_demand_decay S hdec
  have hE : Tendsto E atTop (𝓝 0) := by
    have hh := (((hδ.const_mul 192).sqrt).add (hδ.const_mul 80)).const_mul (2*Real.exp t)
    simpa only [mul_zero,Real.sqrt_zero,add_zero] using hh
  have hlog : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine ⟨ht,?_⟩
  filter_upwards [eventually_ge_atTop 3,hS,hlog.eventually_ge_atTop 1,eventually_wide_window,
    hδ.eventually_le_const (show (0 : ℝ)<1 by norm_num),
    hE.eventually_le_const (show (0 : ℝ)<1 by norm_num),
    (log_power_sqrt_decay 1).eventually_le_const (show (0 : ℝ)<1/96 by norm_num),
    (polynomial_exp_log_limit h).eventually_lt_const (show (0 : ℝ)<1 by norm_num)]
    with N hN hSN hl hw hδN hEN hwidth hexp
  intro m hm
  let w := wideWindow N
  have hn : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hn3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hsp := Real.sqrt_pos.mpr hn
  have hlp : 0<Real.log (N : ℝ) := by linarith
  have hwp : (0 : ℝ)<w := by exact_mod_cast hw.1
  have hlo : Real.sqrt N/(16*Real.log N) ≤ w := hw.2.2.2.1
  have hlowpos : 0<Real.sqrt N/(16*Real.log N) := by positivity
  have hδnon : 0 ≤ δ N := by dsimp only [δ]; positivity
  have hlog2 : 1 ≤ (Real.log (N : ℝ))^2 := one_le_pow₀ hl
  have hlog12 : Real.log (N : ℝ) ≤ (Real.log (N : ℝ))^2 := by nlinarith
  have hsqrt : Real.sqrt (N : ℝ) ≤ N := Real.sqrt_le_iff.mpr ⟨hn.le,by nlinarith⟩
  have hSsqrt : S N ≤ Real.sqrt N := by
    have hh := (div_le_iff₀ hsp).mp hδN
    have h1 := mul_le_mul_of_nonneg_left hlog2 (show 0 ≤ S N+1 by linarith)
    nlinarith
  have hmN : m ≤ N := by exact_mod_cast hm.trans (hSsqrt.trans hsqrt)
  have hratio : 12*((m : ℝ)+1)*Real.log N/(w : ℝ) ≤ 192*δ N := by
    calc
      _ ≤ 12*((m : ℝ)+1)*Real.log N/(Real.sqrt N/(16*Real.log N)) :=
        div_le_div_of_nonneg_left (by positivity) hlowpos hlo
      _ = 192*((m : ℝ)+1)*(Real.log N)^2/Real.sqrt N := by field_simp; ring
      _ ≤ 192*δ N := by
        dsimp only [δ]
        have hh := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (show (m : ℝ)+1 ≤ S N+1 by linarith)
            (sq_nonneg (Real.log (N : ℝ)))) hsp.le
        convert mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 192) using 1
        ring
  have hmratio : (m : ℝ)/w ≤ 16*δ N := by
    calc
      _ ≤ (m : ℝ)/(Real.sqrt N/(16*Real.log N)) :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg m) hlowpos hlo
      _ = 16*(m : ℝ)*Real.log N/Real.sqrt N := by field_simp
      _ ≤ 16*δ N := by
        dsimp only [δ]
        have hh := mul_le_mul (show (m : ℝ) ≤ S N+1 by linarith) hlog12 (by linarith)
          (show 0 ≤ S N+1 by linarith)
        have hh' := div_le_div_of_nonneg_right hh hsp.le
        convert mul_le_mul_of_nonneg_left hh' (by norm_num : (0 : ℝ) ≤ 16) using 1
        ring
  have hpref := (interval_mass_ratio_bound N m w hN hl hmN hw.1 hw.2.1).trans
    (Real.sqrt_le_sqrt hratio)
  have hmean : Real.exp t*((∑ i∈Finset.range (m*w), profile i)+5*m)/((w : ℝ)/2) ≤ 1 := by
    have he : Real.exp t*((∑ i∈Finset.range (m*w), profile i)+5*m)/((w : ℝ)/2) =
        2*Real.exp t*((∑ i∈Finset.range (m*w), profile i)/(w : ℝ)+5*((m : ℝ)/w)) := by ring
    rw [he]
    have hh : (∑ i∈Finset.range (m*w), profile i)/(w : ℝ)+5*((m : ℝ)/w) ≤
        Real.sqrt (192*δ N)+80*δ N := by linarith
    exact (mul_le_mul_of_nonneg_left hh (by positivity)).trans hEN
  constructor
  · simp only [pow_one] at hwidth
    have hh := (div_le_iff₀ hsp).mp hwidth
    have h6 : (6 : ℝ) ≤ Real.sqrt N/(16*Real.log N) := by
      apply (le_div_iff₀ (by positivity)).mpr
      linarith
    change (w : ℝ)/2+3 ≤ w
    linarith
  · have htilt : t*(ε*Real.log N/10)=2*((h : ℝ)+1)*Real.log N := by
      dsimp only [t]
      field_simp
      ring
    have he : Real.exp
        (Real.exp t*((∑ i∈Finset.range (m*wideWindow N), profile i)+5*m)/((wideWindow N : ℝ)/2)-
          t*(ε*Real.log N/10)) ≤ Real.exp (1-2*((h : ℝ)+1)*Real.log N) := by
      apply Real.exp_le_exp.mpr
      rw [htilt]
      exact sub_le_sub_right hmean _
    exact (mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ (N : ℝ)^h+1)).trans_lt hexp

lemma power_demand_decay (a : ℝ) (ha : a<1/2) :
    Tendsto (fun N : ℕ ↦ (N : ℝ)^a*(Real.log N)^2/Real.sqrt N) atTop (𝓝 0) := by
  have hh := (isLittleO_log_rpow_rpow_atTop (2 : ℝ)
    (show (0 : ℝ)<1/2-a by linarith)).tendsto_div_nhds_zero.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNp : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  dsimp only [Function.comp_def]
  rw [Real.sqrt_eq_rpow,Real.rpow_sub hNp]
  norm_num only [Real.rpow_two]
  field_simp

end Erdos66WideRankRestorationBudget
