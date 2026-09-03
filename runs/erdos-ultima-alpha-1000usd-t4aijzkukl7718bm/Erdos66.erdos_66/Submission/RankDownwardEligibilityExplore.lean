import Submission.BoundaryCorrectionEligibilityExplore
import Submission.FlexibleRankDownwardRepairExplore

/-! Exact harmonic brackets leave at most two upper endpoints within the
excluded midpoint margin. This quantifies the capacity for rank relocation. -/
namespace Erdos66RankDownwardEligibility
open AdditiveCombinatorics Erdos66BoundaryCorrectionEligibility
  Erdos66BoundaryPairCounts Erdos66CentralTripleDeletion
  Erdos66ClampedPrefixContinuation Erdos66Fractional
  Erdos66ShortSupportSwapTail Erdos66ReflectionRoundingPatch
open scoped Classical
set_option maxHeartbeats 2200000

noncomputable def eligible (A : Set ℕ) (T n w : ℕ) : Finset ℕ :=
  (upperEndpoints A T n).filter (fun a ↦ n+2*w < 2*a)

lemma near_midpoint_card (A : Set ℕ) (N T n w : ℕ)
    (hbr : ∀ L, PrefixBrackets profile A L) (hn : 4*N ≤ n)
    (hmass : (w : ℝ)*profile N ≤ 1/4) :
    ((upperEndpoints A T n).filter (fun a ↦ ¬n+2*w < 2*a)).card ≤ 2 := by
  let S := (upperEndpoints A T n).filter (fun a ↦ ¬n+2*w < 2*a)
  have hsub : S ⊆ intervalPart A (n/2+1) (n/2+1+w) := by
    intro a ha
    obtain ⟨ha,hmargin⟩ := Finset.mem_filter.mp ha
    obtain ⟨han,hTa,hTb,haA,hbA,hupper⟩ := mem_upperEndpoints.mp ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega,by omega⟩,haA⟩
  have hb := antitone_window_count profile A 1 profile_antitone
    (brackets_count_discrepancy profile A hbr) (n/2+1) w
  have hp := mul_le_mul_of_nonneg_left (profile_antitone (show N ≤ n/2+1 by omega))
    (Nat.cast_nonneg w)
  have hc : (S.card : ℝ) ≤ (intervalPart A (n/2+1) (n/2+1+w)).card :=
    by exact_mod_cast Finset.card_le_card hsub
  change S.card ≤ 2
  by_contra hh
  have h3 : (3 : ℝ) ≤ S.card := by exact_mod_cast (show 3 ≤ S.card by omega)
  linarith

lemma eligible_capacity (A : Set ℕ) (N d n w : ℕ) (hd : 2 ≤ d)
    (hbr : ∀ L, PrefixBrackets profile A L) (hn : 4*N ≤ n)
    (hmass : (w : ℝ)*profile N ≤ 1/4) :
    sumRep A n ≤ 2*(eligible A (n/d^2) n w).card+2*(boundary A d n).card+5 := by
  have hc := central_capacity A d n hd
  have hnear := near_midpoint_card A N (n/d^2) n w hbr hn hmass
  have hs := Finset.card_filter_add_card_filter_not
    (s := upperEndpoints A (n/d^2) n) (p := fun a ↦ n+2*w < 2*a)
  change (eligible A (n/d^2) n w).card+_=_ at hs
  omega

/-- The purely cardinal part of the clipping step, before reinsertion. -/
theorem exists_eligible_clipping_set (A : Set ℕ) (N d n w q : ℕ) (hd : 2 ≤ d)
    (hbr : ∀ L, PrefixBrackets profile A L) (hn : 4*N ≤ n)
    (hmass : (w : ℝ)*profile N ≤ 1/4)
    (hq : 2*(boundary A d n).card+6 ≤ q) :
    ∃ D : Finset ℕ, D ⊆ endpoints A (n/d^2) n ∧
      (∀ a∈D, n+2*w < 2*a) ∧ D.card ≤ sumRep A n ∧
      sumRep A n-2*D.card ≤ q ∧
      min (sumRep A n) (q-1) ≤ sumRep A n-2*D.card := by
  by_cases hr : sumRep A n ≤ q
  · refine ⟨∅,Finset.empty_subset _,by simp,by simp,by simpa using hr,?_⟩
    simp
  let k := (sumRep A n-q+1)/2
  have hcap := eligible_capacity A N d n w hd hbr hn hmass
  have hk : k ≤ (eligible A (n/d^2) n w).card := by dsimp only [k]; omega
  obtain ⟨D,hD,hcard⟩ := Finset.exists_subset_card_eq hk
  refine ⟨D,?_,?_,?_,?_,?_⟩
  · intro a ha
    exact (Finset.filter_subset _ _) ((Finset.filter_subset _ _) (hD ha))
  · intro a ha
    exact (Finset.mem_filter.mp (hD ha)).2
  · dsimp only [k] at hcard
    omega
  · dsimp only [k] at hcard
    omega
  · dsimp only [k] at hcard
    omega

end Erdos66RankDownwardEligibility
