import Submission.RestoredInterceptPrefixExplore
import Submission.InterceptSelectionScaleExplore

/-! At witness density the pruning cost is negligible, whereas the cubic
incidence certificate is still too weak. Neither assertion is a disproof. -/
namespace Erdos66RestoredInterceptScale
open Erdos66Counting Erdos66InterceptSelectionScale
open Filter AdditiveCombinatorics
open scoped Topology
set_option maxHeartbeats 1800000

lemma pruning_relative_cost_bound (p h r : ℝ) (hp : 0 < p) (hh : 0 < h)
    (hr : p*r ≤ 3*h^2) : (4*h+2)*r/h^2 ≤ (12*h+6)/p := by
  apply (div_le_div_iff₀ (sq_pos_of_pos hh) hp).mpr
  have hm := mul_le_mul_of_nonneg_left hr (show 0 ≤ 4*h+2 by positivity)
  nlinarith only [hm]

lemma pruning_envelope_limit {A : Set ℕ} {c : ℝ}
    (ht : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c)) :
    Tendsto (fun N ↦ (12*(count A N : ℝ)+6)/N) atTop (𝓝 0) := by
  have h1 := (count_div_nat_limit_zero ht).const_mul 12
  have h2 := tendsto_const_div_atTop_nhds_zero_nat (6:ℝ)
  have hh := h1.add h2
  simpa only [mul_zero,add_zero,add_div,mul_div_assoc] using hh

/-- Any sequence of pruning counts satisfying the selected budget has a
negligible relative error at the counting profile of a hypothetical witness. -/
theorem pruning_cost_negligible {A : Set ℕ} {c : ℝ} (hc : c≠0)
    (ht : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c))
    (r : ℕ → ℕ) (hr : ∀ᶠN : ℕ in atTop, N*r N ≤ 3*(count A N)^2) :
    Tendsto (fun N ↦ (4*(count A N : ℝ)+2)*r N/(count A N : ℝ)^2) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ by positivity)) ?_ (pruning_envelope_limit ht)
  filter_upwards [hr,count_square_eventually_gt_cutoff hc ht,eventually_ge_atTop 1] with N hr hcount hN
  have hn : (0:ℝ) < N := by exact_mod_cast (show 0<N by omega)
  have hh : (0:ℝ) < count A N := by
    have hh' : 0<count A N := by nlinarith
    exact_mod_cast hh'
  exact pruning_relative_cost_bound N (count A N) (r N) hn hh (by exact_mod_cast hr)

lemma count_cube_div_cutoff_tends_atTop {A : Set ℕ} {c : ℝ} (hc : c≠0)
    (ht : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c)) :
    Tendsto (fun N ↦ (count A N : ℝ)^3/N) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  obtain ⟨k,hk⟩ := exists_nat_gt b
  filter_upwards [count_square_eventually_gt_cutoff hc ht,eventually_ge_atTop ((k+1)^2)] with N hN hlarge
  have hcount : k+1 ≤ count A N := by nlinarith
  have hn : (0:ℝ) < N := by
    have hn' : 0<N := by nlinarith
    exact_mod_cast hn'
  have hh : (0:ℝ) < count A N := by
    have hh' : 0<count A N := by omega
    exact_mod_cast hh'
  have hsq : (N:ℝ) < (count A N : ℝ)^2 := by exact_mod_cast hN
  have hb : b ≤ count A N := hk.le.trans (by exact_mod_cast (show k ≤ count A N by omega))
  apply (le_div_iff₀ hn).mpr
  have hm := mul_lt_mul_of_pos_right hsq hh
  have hm' := mul_le_mul_of_nonneg_right hb hn.le
  nlinarith only [hm,hm']

/-- The sufficient inequality that turns the cubic bound into a small
relative error fails at full-prefix density, for every fixed tolerance.
It says nothing about the actual size of the correction. -/
theorem cubic_certificate_fails_for_full_prefix {A : Set ℕ} {c : ℝ} (hc : c≠0)
    (ht : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c)) (ε : ℝ) :
    ∀ᶠ N : ℕ in atTop, ¬5184*(count A N : ℝ)^3 ≤ (N:ℝ)*ε^3 := by
  have hh := (count_cube_div_cutoff_tends_atTop hc ht).eventually_gt_atTop (ε^3/5184)
  filter_upwards [hh,eventually_ge_atTop 1] with N hN hN1
  have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hmul := (lt_div_iff₀ hn).mp hN
  intro hbad
  nlinarith only [hmul,hbad]

end Erdos66RestoredInterceptScale
