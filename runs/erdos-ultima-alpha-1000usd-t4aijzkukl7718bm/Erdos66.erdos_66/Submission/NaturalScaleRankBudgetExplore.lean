import Submission.NaturalScaleRankWindowExplore

/-! The aggregate restoration potential is feasible at every fixed power
strictly below the square-root demand scale. -/
namespace Erdos66NaturalScaleRankBudget
open Filter Erdos66Fractional Erdos66NaturalScaleRankWindow Erdos66LogCellWindowBudget
  Erdos66RepairParameters
open scoped Topology
set_option maxHeartbeats 4500000

lemma augmented_demand_decay (S : ℕ → ℝ)
    (hdec : Tendsto (fun N : ℕ ↦ S N/Real.sqrt ((N : ℝ)*Real.log N)) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ ↦ (S N+1)/Real.sqrt ((N : ℝ)*Real.log N)) atTop (𝓝 0) := by
  have hh := hdec.add inverse_count_scale_decay
  simp only [add_zero] at hh
  convert hh using 1
  ext N
  ring

/-- Any demand negligible relative to sqrt(N log N) has sublogarithmic total
insertion mean, uniformly over all smaller actual demands. -/
theorem eventually_natural_scale_rank_budget (S : ℕ → ℝ) (hS : ∀ᶠ N in atTop, 0 ≤ S N)
    (hdec : Tendsto (fun N : ℕ ↦ S N/Real.sqrt ((N : ℝ)*Real.log N)) atTop (𝓝 0))
    (ε : ℝ) (hε : 0<ε) (h : ℕ) :
    let t : ℝ := 40*((h : ℝ)+1)/ε
    0<t ∧ ∀ᶠ N : ℕ in atTop, ∀ m : ℕ, (m : ℝ) ≤ S N →
      (densityWindow N : ℝ)/2+3 ≤ densityWindow N ∧
      ((N : ℝ)^h+1)*Real.exp
        (Real.exp t*((∑ i∈Finset.range (m*densityWindow N), profile i)+5*m)/((densityWindow N : ℝ)/2)-
          t*(ε*Real.log N/10))<1 := by
  dsimp only
  let t : ℝ := 40*((h : ℝ)+1)/ε
  let δ (N : ℕ) := (S N+1)/Real.sqrt ((N : ℝ)*Real.log N)
  let E (N : ℕ) := 2*Real.exp t*(Real.sqrt (192*δ N)+80*δ N)
  have ht : 0<t := by dsimp [t]; positivity
  have hδ : Tendsto δ atTop (𝓝 0) := augmented_demand_decay S hdec
  have hE : Tendsto E atTop (𝓝 0) := by
    have hh := (((hδ.const_mul 192).sqrt).add (hδ.const_mul 80)).const_mul (2*Real.exp t)
    simpa only [mul_zero,Real.sqrt_zero,add_zero] using hh
  have hlog : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine ⟨ht,?_⟩
  filter_upwards [eventually_ge_atTop 3,hS,hlog.eventually_ge_atTop 1,eventually_density_window,
    hδ.eventually_le_const (show (0 : ℝ)<1 by norm_num),
    hE.eventually_le_const (show (0 : ℝ)<1 by norm_num),
    (log_power_sqrt_decay 1).eventually_le_const (show (0 : ℝ)<1/96 by norm_num),
    (polynomial_exp_log_limit h).eventually_lt_const (show (0 : ℝ)<1 by norm_num)]
    with N hN hSN hl hw hδN hEN hwidth hexp
  intro m hm
  let w := densityWindow N
  have hn : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hn3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hsp := Real.sqrt_pos.mpr hn
  have hlp : 0<Real.log (N : ℝ) := by linarith
  have hwp : (0 : ℝ)<w := by exact_mod_cast hw.1
  have hlo : Real.sqrt N/(16*Real.sqrt (Real.log N)) ≤ w := hw.2.2.2.1
  have hlowpos : 0<Real.sqrt N/(16*Real.sqrt (Real.log N)) := by positivity
  have hδnon : 0 ≤ δ N := by dsimp only [δ]; positivity
  have hscale : 0<Real.sqrt ((N : ℝ)*Real.log N) := by positivity
  have hslogpos : 0<Real.sqrt (Real.log (N : ℝ)) := by positivity
  have hslog : Real.sqrt (Real.log (N : ℝ)) ≤ Real.log N := Real.sqrt_le_iff.mpr ⟨hlp.le,by nlinarith⟩
  have hslog2 := Real.sq_sqrt hlp.le
  have hscaleN : Real.sqrt ((N : ℝ)*Real.log N) ≤ N := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨hn.le,?_⟩
    have hh := mul_le_mul_of_nonneg_left (Real.log_le_self hn.le) hn.le
    nlinarith only [hh]
  have hSscale : S N ≤ Real.sqrt ((N : ℝ)*Real.log N) := by
    have hh := (div_le_iff₀ hscale).mp hδN
    linarith
  have hmN : m ≤ N := by exact_mod_cast hm.trans (hSscale.trans hscaleN)
  have hden : Real.sqrt ((N : ℝ)*Real.log N)/16 ≤ (w : ℝ)*Real.log N := by
    have hh := (div_le_iff₀ (show 0<16*Real.sqrt (Real.log (N : ℝ)) by positivity)).mp hlo
    have hh' := mul_le_mul_of_nonneg_right hh hslogpos.le
    rw [Real.sqrt_mul hn.le]
    nlinarith only [hh',hslog2]
  have hdenpos : 0<Real.sqrt ((N : ℝ)*Real.log N)/16 := by positivity
  have hratio : 12*((m : ℝ)+1)/((w : ℝ)*Real.log N) ≤ 192*δ N := by
    calc
      _ ≤ 12*((m : ℝ)+1)/(Real.sqrt ((N : ℝ)*Real.log N)/16) :=
        div_le_div_of_nonneg_left (by positivity) hdenpos hden
      _ = 192*((m : ℝ)+1)/Real.sqrt ((N : ℝ)*Real.log N) := by ring
      _ ≤ 192*δ N := by
        dsimp only [δ]
        have hh := div_le_div_of_nonneg_right (show (m : ℝ)+1 ≤ S N+1 by linarith) hscale.le
        convert mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 192) using 1
        ring
  have hmratio : (m : ℝ)/((w : ℝ)*Real.log N) ≤ 16*δ N := by
    calc
      _ ≤ (m : ℝ)/(Real.sqrt ((N : ℝ)*Real.log N)/16) :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg m) hdenpos hden
      _ = 16*(m : ℝ)/Real.sqrt ((N : ℝ)*Real.log N) := by ring
      _ ≤ 16*δ N := by
        dsimp only [δ]
        have hh := div_le_div_of_nonneg_right (show (m : ℝ) ≤ S N+1 by linarith) hscale.le
        convert mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 16) using 1
        ring
  have hpref := (normalized_interval_mass_bound N m w hN hl hmN hw.1 hw.2.1).trans
    (Real.sqrt_le_sqrt hratio)
  have hmean : Real.exp t*((∑ i∈Finset.range (m*w), profile i)+5*m)/((w : ℝ)/2) ≤ Real.log N := by
    apply (div_le_one hlp).mp
    have he : Real.exp t*((∑ i∈Finset.range (m*w), profile i)+5*m)/((w : ℝ)/2)/Real.log N =
        2*Real.exp t*((∑ i∈Finset.range (m*w), profile i)/((w : ℝ)*Real.log N)+
          5*((m : ℝ)/((w : ℝ)*Real.log N))) := by ring
    rw [he]
    have hh : (∑ i∈Finset.range (m*w), profile i)/((w : ℝ)*Real.log N)+
        5*((m : ℝ)/((w : ℝ)*Real.log N)) ≤ Real.sqrt (192*δ N)+80*δ N := by linarith
    exact (mul_le_mul_of_nonneg_left hh (by positivity)).trans hEN
  constructor
  · simp only [pow_one] at hwidth
    have hh := (div_le_iff₀ hsp).mp hwidth
    have h6 : (6 : ℝ) ≤ Real.sqrt N/(16*Real.sqrt (Real.log N)) := by
      apply (le_div_iff₀ (by positivity)).mpr
      linarith
    change (w : ℝ)/2+3 ≤ w
    linarith
  · have htilt : t*(ε*Real.log N/10)=4*((h : ℝ)+1)*Real.log N := by
      dsimp only [t]
      field_simp
      ring
    have he : Real.exp
        (Real.exp t*((∑ i∈Finset.range (m*densityWindow N), profile i)+5*m)/((densityWindow N : ℝ)/2)-
          t*(ε*Real.log N/10)) ≤ Real.exp (1-2*((h : ℝ)+1)*Real.log N) := by
      apply Real.exp_le_exp.mpr
      rw [htilt]
      have hh := Nat.cast_nonneg (α := ℝ) h
      nlinarith only [hmean,hl,hh,mul_nonneg hh hlp.le]
    exact (mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ (N : ℝ)^h+1)).trans_lt hexp

lemma sqrt_demand_decay (M : ℝ) :
    Tendsto (fun N : ℕ ↦ M*Real.sqrt N/Real.sqrt ((N : ℝ)*Real.log N)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hh0 : Tendsto (fun N : ℕ ↦ (Real.sqrt (Real.log (N : ℝ)))⁻¹) atTop (𝓝 0) :=
    (Real.tendsto_sqrt_atTop.comp hlog).inv_tendsto_atTop
  have hh := hh0.const_mul M
  simp only [mul_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hn : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hs := (Real.sqrt_pos.mpr hn).ne'
  rw [Real.sqrt_mul hn.le]
  field_simp

end Erdos66NaturalScaleRankBudget
