import FormalConjecturesUtil
import Submission.NearOrderCloneMerge
import Submission.MergeBackward
import Submission.DenseSplitWitnesses

/-! Near-order exact witnesses with BOTH full cloning obstructions and
dense split-root witnesses. No rationality or disjointness is asserted. -/
open SimpleGraph Finset Filter Asymptotics
namespace Erdos713JointDenseWitnesses
open Erdos713Cloning Erdos713NearOrderCloneMerge Erdos713MergeBackward
open Erdos713VertexMerging Erdos713DenseSplitWitnesses
set_option maxHeartbeats 2000000

/-- The saturation, sharp minimum degree, backward gap, merger obstruction,
and almost-complete split-root relation all concern ONE selected graph. -/
theorem nearby_joint_witnesses {W : Type*} [Fintype W] (H : SimpleGraph W)
    (hH : H.IsBipartite) (hEdge : ∃ x y, H.Adj x y) {α c a δ ε : ℝ}
    (ha : 1 < α) (ha2 : α < 2) (hc : 0 < c) (hac : a < c*α)
    (hd : 0 < δ) (hε : 0 < ε)
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop]
      (fun n => c*(n : ℝ)^α)) (N D : ℕ) :
    ∀ᶠ k : ℕ in atTop, ∃ (U : Type) (_ : Fintype U) (J : SimpleGraph U),
      N ≤ Fintype.card U ∧
      (1-δ)*(k : ℝ) < Fintype.card U ∧ (Fintype.card U : ℝ) < (1+δ)*k ∧
      H.Free J ∧ Nat.card J.edgeSet = extremalNumber (Fintype.card U) H ∧
      (∀ v, D ≤ Nat.card (J.neighborSet v)) ∧
      (∀ v, a*(Fintype.card U : ℝ)^(α-1) ≤ (Nat.card (J.neighborSet v) : ℝ)) ∧
      (∀ v, SingleFold H J v) ∧
      a*(Fintype.card U : ℝ)^(α-1) < (extremalNumber (Fintype.card U) H : ℝ)-
        (extremalNumber (Fintype.card U-1) H : ℝ) ∧
      (∀ u v, u ≠ v → ∀ hn : ¬ J.Adj u v,
        (Nat.card (J.commonNeighbors u v) : ℝ) ≤ a*(Fintype.card U : ℝ)^(α-1) →
        H ⊑ merge J u v hn) ∧
      (missingPairs H J).card ≤ ε*(Fintype.card U : ℝ)^2 := by
  let b := max a c
  have hb0 : 0 < b := hc.trans_le (le_max_right _ _)
  have hbc : b < c*α := max_lt hac (by nlinarith)
  obtain ⟨M,hM⟩ := eventually_atTop.mp (eventually_few_missing_of_mergers H ha ha2 hc hb0 h hε)
  filter_upwards [nearby_joint_saturated H hH hEdge ha ha2 hc hbc h (max N M) D hd] with k hk
  obtain ⟨U,hU,J,hnNM,hnlo,hnhi,hf,he,hD,hMin,hFold,hBack⟩ := hk
  have hab : a*(Fintype.card U : ℝ)^(α-1) ≤ b*(Fintype.card U : ℝ)^(α-1) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hMerge : ∀ u v, u ≠ v → ∀ hn : ¬ J.Adj u v,
      (Nat.card (J.commonNeighbors u v) : ℝ) ≤ b*(Fintype.card U : ℝ)^(α-1) →
      H ⊑ merge J u v hn := fun _ _ huv hn hsmall =>
    merge_contains_of_backward H J he hBack huv hn hsmall
  refine ⟨U,hU,J,(le_max_left N M).trans hnNM,hnlo,hnhi,hf,he,hD,
    fun v => hab.trans (hMin v),hFold,hab.trans_lt hBack,?_,?_⟩
  · exact fun u v huv hn hsmall => hMerge u v huv hn (hsmall.trans hab)
  · exact hM (Fintype.card U) ((le_max_right N M).trans hnNM) U J rfl hf hMerge

#print axioms nearby_joint_witnesses
end Erdos713JointDenseWitnesses
