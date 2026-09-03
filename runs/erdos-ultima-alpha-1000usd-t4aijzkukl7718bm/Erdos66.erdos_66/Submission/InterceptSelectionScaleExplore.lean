import Submission.GoodInterceptFlatExplore
import Submission.FullFaithfulLiftObstructionExplore

/-! The sufficient field-size condition of the generic-translation selector
cannot hold for a full modular prefix of a hypothetical witness. This is
not a restriction on all possible translations or a disproof of the conjecture. -/
namespace Erdos66InterceptSelectionScale
open Erdos66Counting Erdos66TauberianProfile Erdos66Explore
  Erdos66FullFaithfulLiftObstruction
open Filter AdditiveCombinatorics
open scoped Topology
set_option maxHeartbeats 1800000

lemma count_square_eventually_gt_cutoff {A : Set ℕ} {c : ℝ} (hc : c≠0)
    (ht : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c)) :
    ∀ᶠN : ℕ in atTop, N<(count A N)^2 := by
  have hcpos := limit_pos hc ht
  let d : ℝ := 4*c/Real.pi
  have hd : 0<d := by dsimp [d]; positivity
  have hp := witness_counting_square_profile hc ht
  have hlo := hp.eventually (lt_mem_nhds (show d/2<4*c/Real.pi by change d/2<d; linarith))
  have hlog : Tendsto (fun N : ℕ ↦ Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hl := hlog.eventually (eventually_gt_atTop (2/d))
  filter_upwards [hlo,hl,eventually_ge_atTop 2] with N hN hL hN2
  have hn : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hln : 0<Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1<N by omega))
  have hlow := (lt_div_iff₀ (mul_pos hn hln)).mp hN
  have hbig : 1<(d/2)*Real.log (N : ℝ) := by
    have hh := (div_lt_iff₀ hd).mp hL
    nlinarith only [hh]
  have hmul := mul_lt_mul_of_pos_left hbig hn
  have hs : (N : ℝ)<(count A N : ℝ)^2 := by nlinarith only [hmul,hlow]
  exact_mod_cast hs

/-- Failure of the selector's sufficient inequality is not failure of the
underlying construction, and certainly not nonexistence of witnesses. -/
theorem full_prefix_fails_selector_condition {A : Set ℕ} {c : ℝ} (hc : c≠0)
    (ht : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c)) :
    ∀ᶠN : ℕ in atTop, ¬2*(8*(count A N)^7+(count A N)^2)<N := by
  filter_upwards [count_square_eventually_gt_cutoff hc ht] with N hN
  omega

theorem prime_prefix_fails_selector_condition {A : Set ℕ} {c : ℝ} (hc : c≠0)
    (ht : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c)) :
    ∀ᶠp : ℕ in atTop, ∀hp : p.Prime,
      letI : Fact p.Prime := ⟨hp⟩
      ¬2*(8*(prefixParameters A p).card^7+(prefixParameters A p).card^2)<Fintype.card (ZMod p) := by
  filter_upwards [full_prefix_fails_selector_condition hc ht] with p hp
  intro hpprime
  letI : Fact p.Prime := ⟨hpprime⟩
  simpa only [prefixParameters_card,ZMod.card] using hp

end Erdos66InterceptSelectionScale
