import Submission.FiniteHistoryIncidenceExplore
import Submission.CentralEndpointResetExplore

/-! A far-away representation count is insensitive to an arbitrary finite
history: only old tail points in one reflected short window can contribute. -/
namespace Erdos66FiniteHistoryRepresentation
open AdditiveCombinatorics Erdos66FiniteHistoryIncidence Erdos66CentralEndpointReset
  Erdos66CentralTripleDeletion Erdos66ReflectionRoundingPatch
  Erdos66ClampedPrefixContinuation Erdos66Fractional
open scoped Classical
set_option maxHeartbeats 2400000

lemma history_hit_window (A B : Set ℕ) (U N n : ℕ) (hUN : U ≤ N) (hn : 2*N ≤ n)
    (hagree : ∀ a, U ≤ a → (a∈B ↔ a∈A)) :
    (hits (A∪B) (Finset.range U) n).card ≤ (intervalPart A (n+1-U) (n+1-U+U)).card := by
  apply Finset.card_le_card_of_injOn (fun a : ℕ ↦ n-a)
  · intro a ha
    change a∈hits (A∪B) (Finset.range U) n at ha
    simp only [hits,Finset.mem_filter] at ha
    obtain ⟨ha,han,hpartner⟩ := ha
    have haU := Finset.mem_range.mp ha
    have hbA : n-a∈A := hpartner.elim id ((hagree (n-a) (by omega)).mp)
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega,by omega⟩,hbA⟩
  · intro a ha b hb he
    change a∈hits (A∪B) (Finset.range U) n at ha
    change b∈hits (A∪B) (Finset.range U) n at hb
    simp only [hits,Finset.mem_filter] at ha hb
    have ha' := ha.2.1
    have hb' := hb.2.1
    dsimp only at he
    omega

lemma representation_after_history (A B : Set ℕ) (hbr : ∀ L, PrefixBrackets profile A L)
    (U N n : ℕ) (hUN : U ≤ N) (hn : 2*N ≤ n) (hmass : (U : ℝ)*profile N ≤ 1/2)
    (hagree : ∀ a, U ≤ a → (a∈B ↔ a∈A)) :
    |(sumRep B n : ℝ)-sumRep A n| ≤ 4 := by
  have hh := localized_edit_bound (A∪B) A B (Finset.range U) Set.subset_union_left
    Set.subset_union_right (fun a ha ↦ (hagree a (by simpa only [Finset.mem_range,not_lt] using ha)).symm) n
  have hc := (history_hit_window A B U N n hUN hn hagree).trans
    (small_tail_window A hbr U N (n+1-U) (by omega) hmass)
  have hcR : ((hits (A∪B) (Finset.range U) n).card : ℝ) ≤ 2 := by exact_mod_cast hc
  linarith

end Erdos66FiniteHistoryRepresentation
