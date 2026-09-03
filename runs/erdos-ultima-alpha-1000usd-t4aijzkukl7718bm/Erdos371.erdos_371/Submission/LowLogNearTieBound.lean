import Submission.LogNearTieRanges
import Submission.QuadraticSmoothBound

/-! A CRT upper bound for logarithmic near-ties below the square-root
threshold, with a power-smooth exceptional set. -/

namespace Erdos371
namespace FiniteSieve
open Finset Filter

noncomputable def logPowerIndex (N : ℕ) (a : ℝ) : ℕ :=
  ⌊a*(Real.log N/Real.log 2)⌋₊+1

lemma logPowerIndex_power_bound (N : ℕ) (a : ℝ) (hN : 1 < N) (ha : 0 ≤ a) :
    (2 : ℝ)^(logPowerIndex N a) ≤ 2*(N : ℝ)^a := by
  have hn0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlN : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hf := Nat.floor_le (mul_nonneg ha (div_nonneg hlN.le hl2.le))
  have hp : (2 : ℝ)^⌊a*(Real.log N/Real.log 2)⌋₊ ≤ (N : ℝ)^a := by
    rw [← Real.rpow_natCast]
    calc
      _ ≤ (2 : ℝ)^(a*(Real.log N/Real.log 2)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hf
      _ = _ := by
        rw [Real.rpow_def_of_pos (by norm_num),Real.rpow_def_of_pos hn0]
        congr 1
        field_simp
  dsimp only [logPowerIndex]
  rw [pow_succ]
  nlinarith

lemma comparablePrimeMass_power_width_bound (N D : ℕ) (a δ : ℝ)
    (hN : 1 < N) (ha : 0 < a) (hδ : 0 ≤ δ) :
    comparablePrimeMass ⌈(N : ℝ)^δ⌉₊ (logPowerIndex N a) D ≤
      64*δ/a + 192/(a*(Real.log N/Real.log 2)) := by
  let C := ⌈(N : ℝ)^δ⌉₊
  let L := Nat.log 2 C+1
  let H := Real.log N/Real.log 2
  have hn0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN.le
  have hlN : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hH : 0 < H := div_pos hlN hl2
  have hC0 : 0 < C := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hn0 δ)
  have hCup : (C : ℝ) ≤ 2*(N : ℝ)^δ := by
    have h := Nat.ceil_lt_add_one (Real.rpow_nonneg hn0.le δ)
    have h1 := Real.one_le_rpow hn1 hδ
    dsimp only [C]
    linarith
  have hlogC : Real.log C ≤ Real.log 2+δ*Real.log N := by
    have h := Real.log_le_log (by exact_mod_cast hC0 : (0 : ℝ) < C) hCup
    rwa [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hn0 δ).ne',Real.log_rpow hn0] at h
  have hlogNat : (Nat.log 2 C : ℝ)*Real.log 2 ≤ Real.log C := by
    have hp : (2 : ℝ)^(Nat.log 2 C) ≤ C := by exact_mod_cast Nat.pow_log_le_self 2 hC0.ne'
    simpa only [Real.log_pow] using Real.log_le_log (by positivity) hp
  have hL : (L+1 : ℝ) ≤ δ*H+3 := by
    have hHe : H*Real.log 2 = Real.log N := by dsimp [H]; field_simp
    dsimp only [L]
    push_cast
    nlinarith
  have hA : a*H ≤ (logPowerIndex N a : ℝ) := by
    simpa only [logPowerIndex,Nat.cast_add,Nat.cast_one] using (Nat.lt_floor_add_one (a*H)).le
  have hApos : 0 < logPowerIndex N a := by dsimp [logPowerIndex]; omega
  have hm := comparablePrimeMass_bound C L (logPowerIndex N a) D
    (Nat.lt_pow_succ_log_self (by decide : 1 < 2) C).le hApos
  calc
    _ ≤ 64*(L+1 : ℝ)/(logPowerIndex N a : ℝ) := hm
    _ ≤ 64*(δ*H+3)/(logPowerIndex N a : ℝ) :=
      div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
    _ ≤ 64*(δ*H+3)/(a*H) := div_le_div_of_nonneg_left (by positivity) (mul_pos ha hH) hA
    _ = _ := by change _ = 64*δ/a+192/(a*H); field_simp; ring

lemma logRatio_smooth_cutoff_bound (N : ℕ) (a δ : ℝ)
    (hN : 1 < N) (ha : 0 ≤ a) (hδ : 0 ≤ δ) (hδa : δ ≤ a/2)
    (hscale : 6 ≤ (N : ℝ)^(a/2)) :
    (((⌈(N : ℝ)^δ⌉₊+1)*2^(logPowerIndex N a) : ℕ) : ℝ) ≤ (N : ℝ)^(2*a) := by
  have hn0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN.le
  have hC : (⌈(N : ℝ)^δ⌉₊+1 : ℝ) ≤ 3*(N : ℝ)^δ := by
    have hf := Nat.ceil_lt_add_one (Real.rpow_nonneg hn0.le δ)
    have h1 := Real.one_le_rpow hn1 hδ
    linarith
  push_cast
  calc
    _ ≤ (3*(N : ℝ)^δ)*(2*(N : ℝ)^a) :=
      mul_le_mul hC (logPowerIndex_power_bound N a hN ha) (by positivity) (by positivity)
    _ = 6*(N : ℝ)^(a+δ) := by rw [Real.rpow_add hn0]; ring
    _ ≤ (N : ℝ)^(a/2)*(N : ℝ)^(a+δ) :=
      mul_le_mul_of_nonneg_right hscale (Real.rpow_nonneg hn0.le _)
    _ = (N : ℝ)^(a/2+(a+δ)) := (Real.rpow_add hn0 _ _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)

lemma lowLogRatioSet_eventually_le (α a δ : ℝ)
    (hα : α < 1/2) (ha : 0 < a) (hδ : 0 ≤ δ) (hδa : δ ≤ a/2)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ((lowLogRatioSet N α δ).card : ℝ)/N ≤
      320*a^2 + 64*δ/a + ε := by
  classical
  have hH := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).atTop_div_const
    (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  have ht : Tendsto (fun N : ℕ => 192/(a*(Real.log N/Real.log 2))) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (hH.const_mul_atTop ha)
  have hf := floor_rpow_sq_div_tendsto_zero α hα
  have hpow := (tendsto_rpow_atTop (half_pos ha)).comp tendsto_natCast_atTop_atTop
  filter_upwards [smooth_power_count_eventually_le (2*a) (by positivity) (ε/3) (by positivity),
    ht.eventually_lt_const (by positivity : (0 : ℝ) < ε/3),
    hf.eventually_lt_const (by positivity : (0 : ℝ) < ε/3),
    hpow.eventually (eventually_ge_atTop (6 : ℝ)),eventually_gt_atTop (1 : ℕ)]
    with N hs he hf hscale hN
  have hn0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hcut := logRatio_smooth_cutoff_bound N a δ hN ha.le hδ hδa hscale
  have hcard : (((range N).filter fun n => Nat.maxPrimeFac (n+1) ≤
      (⌈(N : ℝ)^δ⌉₊+1)*2^(logPowerIndex N a)).card : ℝ) ≤
      (((range N).filter fun n => (Nat.maxPrimeFac (n+1) : ℝ) ≤ (N : ℝ)^(2*a)).card : ℝ) := by
    apply Nat.cast_le.mpr
    apply card_le_card
    intro n hn
    obtain ⟨hnN,hp⟩ := mem_filter.mp hn
    exact mem_filter.mpr ⟨hnN,(by exact_mod_cast hp : (Nat.maxPrimeFac (n+1) : ℝ) ≤
      (((⌈(N : ℝ)^δ⌉₊+1)*2^(logPowerIndex N a) : ℕ) : ℝ)).trans hcut⟩
  have hb := lowLogRatioSet_card_bound N (logPowerIndex N a) α δ
  have hm := comparablePrimeMass_power_width_bound N ⌊(N : ℝ)^α⌋₊ a δ hN ha hδ
  have hc := div_le_div_of_nonneg_right (hb.trans (add_le_add
    (add_le_add hcard (mul_le_mul_of_nonneg_left hm hn0.le)) le_rfl)) hn0.le
  have hc' : ((lowLogRatioSet N α δ).card : ℝ)/N ≤
      (((range N).filter fun n => (Nat.maxPrimeFac (n+1) : ℝ) ≤ (N : ℝ)^(2*a)).card : ℝ)/N +
      (64*δ/a + 192/(a*(Real.log N/Real.log 2))) + (⌊(N : ℝ)^α⌋₊ : ℝ)^2/N := by
    convert hc using 1 <;> field_simp
  linarith

#print axioms lowLogRatioSet_eventually_le
end FiniteSieve
end Erdos371
