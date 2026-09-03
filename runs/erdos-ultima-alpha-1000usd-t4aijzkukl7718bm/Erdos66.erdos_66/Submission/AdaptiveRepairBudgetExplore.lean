import Submission.RepairParametersExplore

/-! The coordinated-repair budgets vanish whenever total packet demand times
log(N)/sqrt(N) tends to zero. -/
namespace Erdos66AdaptiveRepairBudget
open Filter Erdos66RepairParameters
open scoped Topology
set_option maxHeartbeats 2400000

lemma log_sqrt_decay : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)/Real.sqrt N) atTop (𝓝 0) := by
  have hh := (isLittleO_log_rpow_atTop (show (0 : ℝ)<1/2 by norm_num)).tendsto_div_nhds_zero.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  simpa only [←Real.sqrt_eq_rpow] using hh

lemma demand_sqrt_decay (S : ℕ → ℝ) (hS : ∀ᶠ N in atTop, 0 ≤ S N)
    (hdec : Tendsto (fun N : ℕ ↦ S N*Real.log N/Real.sqrt N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ ↦ S N/Real.sqrt N) atTop (𝓝 0) := by
  have hlog : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  apply squeeze_zero' _ _ hdec
  · filter_upwards [hS] with N hN
    exact div_nonneg hN (Real.sqrt_nonneg _)
  · filter_upwards [hS,hlog.eventually_ge_atTop 1] with N hN hl
    exact div_le_div_of_nonneg_right (by nlinarith) (Real.sqrt_nonneg _)

lemma demand_nat_decay (S : ℕ → ℝ) (hS : ∀ᶠ N in atTop, 0 ≤ S N)
    (hdec : Tendsto (fun N : ℕ ↦ S N*Real.log N/Real.sqrt N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ ↦ S N/(N : ℝ)) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ (demand_sqrt_decay S hS hdec)
  · filter_upwards [hS] with N hN
    exact div_nonneg hN (Nat.cast_nonneg N)
  · filter_upwards [hS,eventually_ge_atTop 1] with N hN hN1
    have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    have hs : Real.sqrt (N : ℝ) ≤ N := Real.sqrt_le_iff.mpr ⟨by linarith,by nlinarith⟩
    exact div_le_div_of_nonneg_left hN (Real.sqrt_pos.mpr (by linarith)) hs

lemma budget_identity (v s B G : ℝ) (hv : 0<v) :
    (B*Real.sqrt v*Real.log v+4*G*Real.sqrt v*s+s*(B*Real.sqrt v*Real.log v+4*s+2))/v =
      B*(Real.log v/Real.sqrt v)+4*G*(s/Real.sqrt v)+B*(s*Real.log v/Real.sqrt v)+
        4*(s/Real.sqrt v)^2+2*(s/v) := by
  have hs : Real.sqrt v≠0 := (Real.sqrt_pos.mpr hv).ne'
  have hr := Real.sq_sqrt hv.le
  field_simp
  rw [hr]
  ring

lemma mean_budget_identity (v s B t : ℝ) (hv : 0<v) :
    s*Real.exp t*(B*Real.sqrt v*Real.log v+4*s+2)/(v/2) =
      2*Real.exp t*(B*(s*Real.log v/Real.sqrt v)+4*(s/Real.sqrt v)^2+2*(s/v)) := by
  have hs : Real.sqrt v≠0 := (Real.sqrt_pos.mpr hv).ne'
  have hr := Real.sq_sqrt hv.le
  field_simp
  rw [hr]
  ring

lemma adaptive_budget_limits (S : ℕ → ℝ) (hS : ∀ᶠ N in atTop, 0 ≤ S N)
    (hdec : Tendsto (fun N : ℕ ↦ S N*Real.log N/Real.sqrt N) atTop (𝓝 0)) (B G t : ℝ) :
    Tendsto (fun N : ℕ ↦
      (B*Real.sqrt N*Real.log N+4*G*Real.sqrt N*S N+S N*(B*Real.sqrt N*Real.log N+4*S N+2))/N)
      atTop (𝓝 0) ∧
    Tendsto (fun N : ℕ ↦ S N*Real.exp t*(B*Real.sqrt N*Real.log N+4*S N+2)/((N : ℝ)/2))
      atTop (𝓝 0) := by
  have hu := demand_sqrt_decay S hS hdec
  have hv := demand_nat_decay S hS hdec
  constructor
  · have hh := ((((log_sqrt_decay.const_mul B).add (hu.const_mul (4*G))).add
      (hdec.const_mul B)).add ((hu.pow 2).const_mul 4)).add (hv.const_mul 2)
    simp only [mul_zero,add_zero,zero_pow (by omega : 2≠0)] at hh
    apply hh.congr'
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact (budget_identity N (S N) B G (by exact_mod_cast (show 0<N by omega))).symm
  · have hh := (((hdec.const_mul B).add ((hu.pow 2).const_mul 4)).add (hv.const_mul 2)).const_mul (2*Real.exp t)
    simp only [mul_zero,add_zero,zero_pow (by omega : 2≠0)] at hh
    apply hh.congr'
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact (mean_budget_identity N (S N) B t (by exact_mod_cast (show 0<N by omega))).symm

/-- Availability and the common exponential potential are simultaneously
small at the nearly square-root demand scale. -/
theorem eventually_adaptive_budget (S : ℕ → ℝ) (hS : ∀ᶠ N in atTop, 0 ≤ S N)
    (hdec : Tendsto (fun N : ℕ ↦ S N*Real.log N/Real.sqrt N) atTop (𝓝 0))
    (B G ε : ℝ) (hB : 0 ≤ B) (hG : 0 ≤ G) (hε : 0<ε) (h : ℕ) :
    let t : ℝ := 56*((h : ℝ)+1)/ε
    0<t ∧ ∀ᶠ N : ℕ in atTop, ∀ m H c : ℕ,
      (m : ℝ) ≤ S N → (H : ℝ) ≤ G*Real.sqrt N → c ≤ m →
      (N : ℝ)/2+B*Real.sqrt N*Real.log N+4*H*m+c*(B*Real.sqrt N*Real.log N+4*m+2) ≤ N ∧
      ((N : ℝ)^h+1)*Real.exp ((m : ℝ)*Real.exp t*(B*Real.sqrt N*Real.log N+4*m+2)/((N : ℝ)/2)-
        t*(ε*Real.log N/28))<1 := by
  dsimp only
  let t : ℝ := 56*((h : ℝ)+1)/ε
  have ht : 0<t := by dsimp [t]; positivity
  refine ⟨ht,?_⟩
  obtain ⟨ha,hmean⟩ := adaptive_budget_limits S hS hdec B G t
  have he := polynomial_exp_log_limit h
  have hlog : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 1,hS,hlog.eventually_ge_atTop 1,
    ha.eventually_le_const (show (0 : ℝ)<1/2 by norm_num),
    hmean.eventually_le_const (show (0 : ℝ)<1 by norm_num),
    he.eventually_lt_const (show (0 : ℝ)<1 by norm_num)] with N hN hSN hl haN hmN heN
  intro m H c hm hH hc
  have hNp : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hcm : (c : ℝ) ≤ m := by exact_mod_cast hc
  have hnon : 0 ≤ B*Real.sqrt N*Real.log N := by positivity
  have hcost : B*Real.sqrt N*Real.log N+4*H*m+c*(B*Real.sqrt N*Real.log N+4*m+2) ≤
      B*Real.sqrt N*Real.log N+4*G*Real.sqrt N*S N+S N*(B*Real.sqrt N*Real.log N+4*S N+2) := by
    have h1 := mul_le_mul hH hm (Nat.cast_nonneg m) (by positivity : 0 ≤ G*Real.sqrt N)
    have h2 := mul_le_mul (hcm.trans hm) (show B*Real.sqrt N*Real.log N+4*m+2 ≤
        B*Real.sqrt N*Real.log N+4*S N+2 by linarith)
      (by positivity) hSN
    nlinarith
  have hmean' : (m : ℝ)*Real.exp t*(B*Real.sqrt N*Real.log N+4*m+2)/((N : ℝ)/2) ≤ 1 := by
    have hnum := mul_le_mul hm (show B*Real.sqrt N*Real.log N+4*m+2 ≤
        B*Real.sqrt N*Real.log N+4*S N+2 by linarith) (by positivity) hSN
    have hx := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnum (Real.exp_pos t).le)
      (show (0 : ℝ) ≤ N/2 by positivity)
    have heq (r : ℝ) : Real.exp t*(r*(B*Real.sqrt N*Real.log N+4*r+2))/((N : ℝ)/2)=
        r*Real.exp t*(B*Real.sqrt N*Real.log N+4*r+2)/((N : ℝ)/2) := by ring
    rw [heq,heq] at hx
    exact hx.trans hmN
  constructor
  · have hh := (div_le_iff₀ hNp).mp haN
    linarith
  · have htilt : t*(ε*Real.log (N : ℝ)/28)=2*((h : ℝ)+1)*Real.log N := by
      dsimp only [t]
      field_simp
      ring
    have hexp : Real.exp ((m : ℝ)*Real.exp t*(B*Real.sqrt N*Real.log N+4*m+2)/((N : ℝ)/2)-
        t*(ε*Real.log N/28)) ≤ Real.exp (1-2*((h : ℝ)+1)*Real.log N) := by
      apply Real.exp_le_exp.mpr
      rw [htilt]
      linarith
    exact (mul_le_mul_of_nonneg_left hexp (by positivity : (0 : ℝ) ≤ (N : ℝ)^h+1)).trans_lt heN

/-- Every fixed power strictly below one half meets the demand condition. -/
lemma power_demand_decay (a : ℝ) (ha : a<1/2) :
    Tendsto (fun N : ℕ ↦ (N : ℝ)^a*Real.log N/Real.sqrt N) atTop (𝓝 0) := by
  have hh := (isLittleO_log_rpow_atTop (show (0 : ℝ)<1/2-a by linarith)).tendsto_div_nhds_zero.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNp : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  dsimp only [Function.comp_def]
  rw [Real.sqrt_eq_rpow,Real.rpow_sub hNp]
  field_simp

end Erdos66AdaptiveRepairBudget
