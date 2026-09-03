import Submission.MaximalComplementPowerCutoff
import Submission.ExponentialRoughCutoff

/-! A constrained diagonal chooses signed short-complement cancellation and a uniform
small-divisor prefix budget simultaneously. -/
namespace Erdos371
open Finset Filter
open scoped Topology

lemma exists_maximal_complement_prefix_row (d k : ℕ) :
    ∃ B : ℕ → ℕ, ∃ L : ℕ, ∀ᶠ N : ℕ in atTop,
      k≤B N ∧ 1≤B N ∧ (k+1)*N≤(B N+1)^L ∧
      Real.log (B N+1 : ℝ)/Real.log N≤2/(k+1 : ℝ) ∧
      (∀ X ≤ (B N)^d, |(∑ n ∈ range N, untruncatedComplementPrefix (B N) X n)/N|≤1/(k+1 : ℝ)) ∧
      roughPrefixBudget (B N) L ((k+1)*N)/N≤1/(k+1 : ℝ) := by
  classical
  obtain ⟨u,hu,_,hex⟩ := exists_power_cutoff_maximal_complement_cancellation d (1/(k+1 : ℝ)) (1/(k+1 : ℝ))
    (by positivity) (by positivity)
  let Good (N B : ℕ) : Prop := (N : ℝ)^u≤B ∧ (B : ℝ)≤(N : ℝ)^(1/(k+1 : ℝ)) ∧
    ∀ X ≤ B^d, |(∑ n ∈ range N, untruncatedComplementPrefix B X n)/N|<1/(k+1 : ℝ)
  let B (N : ℕ) : ℕ := if h : ∃ b, Good N b then Classical.choose h else 0
  have hgood : ∀ᶠ N in atTop, Good N (B N) := by
    filter_upwards [hex] with N hN
    have h : ∃ b, Good N b := hN
    dsimp only [B]
    rw [dif_pos h]
    exact Classical.choose_spec h
  have hB : Tendsto B atTop atTop := by
    apply tendsto_atTop.mpr
    intro M
    have hp := ((tendsto_rpow_atTop hu).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (M : ℝ)
    filter_upwards [hgood,hp] with N hg hp
    exact_mod_cast hp.trans hg.1
  obtain ⟨l,hl⟩ := (tendsto_one_div_add_atTop_nhds_zero_nat.eventually_lt_const hu).exists
  let L := (l+1)*2
  have hsize : ∀ᶠ N in atTop, (k+1)*N≤(B N+1)^L := by
    filter_upwards [hgood,eventually_ge_atTop (max 1 (k+1))] with N hg hN
    have hN1 : (1 : ℝ)≤N := by exact_mod_cast (le_max_left 1 (k+1)).trans hN
    have hr : rootRoughCutoff l N≤B N := by
      apply Nat.ceil_le.mpr
      exact (Real.rpow_le_rpow_of_exponent_le hN1 hl.le).trans hg.1
    have hp : N≤(B N+1)^(l+1) := (rootRoughCutoff_power l N).trans
      (Nat.pow_le_pow_left (hr.trans (Nat.le_succ _)) _)
    calc
      _ ≤ N*N := Nat.mul_le_mul_right N ((le_max_right 1 (k+1)).trans hN)
      _ ≤ ((B N+1)^(l+1))*((B N+1)^(l+1)) := Nat.mul_le_mul hp hp
      _ = _ := by dsimp [L]; rw [pow_mul,pow_two]
  have hlog : ∀ᶠ N in atTop, Real.log (B N+1 : ℝ)/Real.log N≤2/(k+1 : ℝ) := by
    filter_upwards [hgood,rootRoughCutoff_log_eventually_le k] with N hg hr
    have hle : B N≤rootRoughCutoff k N := by
      have hh := hg.2.1.trans (Nat.le_ceil ((N : ℝ)^(1/(k+1 : ℝ))))
      change B N≤⌈(N : ℝ)^(1/(k+1 : ℝ))⌉₊
      exact_mod_cast hh
    apply le_trans _ hr
    apply div_le_div_of_nonneg_right _ (Real.log_natCast_nonneg N)
    apply Real.log_le_log (by positivity)
    exact_mod_cast Nat.add_le_add_right hle 1
  have hbudget := roughPrefixBudget_fixed_multiple_tendsto B L (k+1) (by omega) hB
  refine ⟨B,L,?_⟩
  filter_upwards [hgood,hsize,hlog,hB.eventually_ge_atTop k,hB.eventually_ge_atTop 1,
    hbudget.eventually_lt_const (show (0 : ℝ)<1/(k+1 : ℝ) by positivity)] with N hg hs hl hk h1 hb
  exact ⟨hk,h1,hs,hl,(fun X hX => (hg.2.2 X hX).le),hb.le⟩


#print axioms exists_maximal_complement_prefix_row
end Erdos371
