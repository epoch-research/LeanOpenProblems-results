import Submission.RankDownwardEligibilityExplore

/-! Boundary-controlled downward clipping preserves the original exact
brackets and has uniformly small collateral at every other target. -/
namespace Erdos66ExactBracketDownwardClipping
open Filter AdditiveCombinatorics Erdos66RankDownwardEligibility
  Erdos66FlexibleRankDownwardRepair Erdos66LogCellWindowBudget
  Erdos66ClampedPrefixContinuation Erdos66Fractional Erdos66BoundaryPairCounts
  Erdos66CentralTripleCounts Erdos66OrderedPartialReplacement
  Erdos66PredecessorCandidateDegree Erdos66PredecessorCutoffTransfer
  Erdos66PredecessorScaleBudget
open scoped Classical Topology
set_option maxHeartbeats 3000000

theorem uniformly_eventually_downward_clipping (K C ε : ℝ) (R : ℕ)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ A : Set ℕ,
      (∀ L, PrefixBrackets profile A L) →
      (∀ z, (sumRep A z : ℝ) ≤ K+C*Real.log ((z : ℝ)+2)) →
      ∀ d n q : ℕ, 2 ≤ d → 4*N ≤ n → n ≤ 5*N →
      (∀ z, z ≤ N^33 → n≠z → (fiber A (n/d^2) n z).card ≤ R) →
      2*(boundary A d n).card+6 ≤ q →
      ∃ D F : Finset ℕ, F.card=D.card ∧ Disjoint (F : Set ℕ) A ∧
        (∀ u∈D∪F, N ≤ u ∧ u ≤ 6*N) ∧
        (∀ L, PrefixBrackets profile (swap A D F) L) ∧
        min (sumRep A n) (q-1) ≤ sumRep (swap A D F) n ∧
        sumRep (swap A D F) n ≤ q ∧
        ∀ z, z≠n → |(sumRep (swap A D F) z : ℝ)-sumRep A z| ≤ ε*Real.log ((z : ℝ)+2) := by
  let M : ℝ := K+C*((33 : ℕ)+6)+1
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hlog : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [uniformly_eventually_downward_rank_repair K C M ε R hK hC hM hε,
    eventually_window_mass,eventually_ge_atTop 32,hlog.eventually_ge_atTop 1]
    with N hrepair hwm hN hl
  intro A hbr henv d n q hd hnlo hnhi htr hq
  obtain ⟨D,hDE,hmargin,hcard,hupper,hlower⟩ :=
    exists_eligible_clipping_set A N d n (windowSize N) q hd hbr hnlo hwm.2.2 hq
  have hXX : 5*N < N^33+1 := by
    have hp := Nat.pow_le_pow_right (by omega : 0 < N) (show 2 ≤ 33 by norm_num)
    have hh : 5*N ≤ N^2 := by nlinarith
    omega
  have hcap := finite_profile_envelope A K C hK hC henv N 33 (by omega) hl n
  rw [cutoff_rep A (by omega)] at hcap
  have hcardR : (D.card : ℝ) ≤ sumRep A n := by exact_mod_cast hcard
  have hm : (D.card : ℝ) ≤ M*Real.log N := hcardR.trans hcap
  obtain ⟨F,hFc,hFA,hs,hbr',hexact,hchange⟩ :=
    hrepair A hbr henv (n/d^2) n hnlo hnhi htr D hDE hm hmargin
  refine ⟨D,F,hFc,hFA,hs,hbr',?_,?_,hchange⟩ <;> omega

end Erdos66ExactBracketDownwardClipping
