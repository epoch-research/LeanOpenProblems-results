import Submission.PrefixBalancedPaletteExplore

/-! Spatially balanced finite palettes with room for a prescribed bounded
range of cardinality multipliers. The modulus is chosen after that range. -/
namespace Erdos66BoundedWeightPalette
open Filter Erdos66PrefixBalancedPalette Erdos66OuterMixedPrefix Erdos66SaturatingCyclicFamily
open scoped Classical Topology
set_option maxHeartbeats 2400000

theorem exists_fitting_prefix_palette (c τ η ε W : ℝ)
    (hc : 0<c) (hτ : 0<τ) (hη : 0<η) (hη1 : η ≤ 1)
    (hε : 0<ε) (hε1 : ε ≤ 1) (hW : 0 ≤ W) (N₀ : ℕ) :
    ∃ M : ℕ, N₀<M ∧ 1<M ∧ ∃ hM : NeZero M,
      ∃ (B : Finset (ZMod M)) (P : Finset (Finset (ZMod M))),
        0<B.card ∧ B∈P ∧ W*(B.card:ℝ) ≤ M ∧
        |actualMean M B B/Real.log M-c|<τ ∧
        (∀ C∈P, ∀ D∈P, ∀ z u, u ≤ M →
          |(prefixCount M C D z u:ℝ)-(u:ℝ)/M*actualMean M C D| ≤ η*actualMean M C D) ∧
        (∀ x : ℝ, (B.card:ℝ) ≤ x → x ≤ M →
          ∃ C∈P, x ≤ (C.card:ℝ) ∧ (C.card:ℝ) ≤ (1+ε)*x) := by
  have hlim : Tendsto (fun M : ℕ ↦ W^2*(c+τ)*Real.log M/(M:ℝ)) atTop (𝓝 0) := by
    have hh := (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
      (tendsto_natCast_atTop_atTop (R:=ℝ))).const_mul (W^2*(c+τ))
    simpa only [Function.comp_apply,id_eq,mul_zero,mul_div_assoc] using hh
  obtain ⟨L,hL⟩ := eventually_atTop.mp (hlim.eventually_le_const (by norm_num : (0:ℝ)<1))
  obtain ⟨M,hMN,hodd,hM,B,P,hBpos,hBmem,htune,hBsub,hnest,hflat,hprefix,hfull,hPcard,hcover⟩ :=
    exists_prefix_balanced_complete_palette c τ η ε hc hτ hη hη1 hε hε1 (max N₀ (max L 2))
  letI := hM
  have hM1 : 1<M := by omega
  have hMr : (0:ℝ)<M := by exact_mod_cast (show 0<M by omega)
  have hlog : 0<Real.log (M:ℝ) := Real.log_pos (by exact_mod_cast hM1)
  have hμup : actualMean M B B ≤ (c+τ)*Real.log M := by
    apply (div_le_iff₀ hlog).mp
    have hh := (abs_lt.mp htune).2
    linarith
  have hq2 : (B.card:ℝ)^2 ≤ (c+τ)*Real.log M*M := by
    have hh := (div_le_iff₀ hMr).mp hμup
    nlinarith only [hh]
  have hbudget : W^2*(c+τ)*Real.log M ≤ M := by
    have hh := (div_le_iff₀ hMr).mp (hL M (by omega))
    simpa only [one_mul] using hh
  have hfit : W*(B.card:ℝ) ≤ M := by
    apply le_of_sq_le_sq _ hMr.le
    have hh1 := mul_le_mul_of_nonneg_left hq2 (sq_nonneg W)
    have hh2 := mul_le_mul_of_nonneg_right hbudget hMr.le
    nlinarith only [hh1,hh2]
  exact ⟨M,by omega,hM1,hM,B,P,hBpos,hBmem,hfit,htune,hprefix,hcover⟩

end Erdos66BoundedWeightPalette
