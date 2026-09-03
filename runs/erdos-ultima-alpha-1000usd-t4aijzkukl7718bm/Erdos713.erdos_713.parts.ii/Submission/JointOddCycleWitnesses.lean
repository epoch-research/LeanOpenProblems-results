import FormalConjecturesUtil
import Submission.JointDenseWitnesses
import Submission.ContractionOddCycles

/-! Short odd cycles on the SAME exact near-order hosts as the full-clone
and dense split-root witnesses. No exponent improvement is asserted. -/
open SimpleGraph Finset Filter Asymptotics
namespace Erdos713JointOddCycleWitnesses
open Erdos713Cloning Erdos713JointDenseWitnesses
open Erdos713VertexMerging Erdos713DenseSplitWitnesses
open Erdos713ContractionOddCycles
set_option maxHeartbeats 2000000

/-- Under the explicit nonseparation condition on H, all of these
properties hold on one exact host in each sufficiently large relative
order window. The cycles are not asserted to be disjoint. -/
theorem nearby_joint_odd_witnesses {W : Type*} [Fintype W] (H : SimpleGraph W)
    (hH : H.IsBipartite) (hEdge : ∃ x y, H.Adj x y)
    (hRest : ∀ w, (H.induce {w}ᶜ).Preconnected) {α c a δ ε : ℝ}
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
      (missingPairs H J).card ≤ ε*(Fintype.card U : ℝ)^2 ∧
      (∀ u v, J.Adj u v → ∃ p : J.Walk u u,
        p.IsCycle ∧ Odd p.length ∧ p.length ≤ Fintype.card W+1 ∧ s(u,v) ∈ p.edges) := by
  let b := max a c
  have hb0 : 0 < b := hc.trans_le (le_max_right _ _)
  have hbc : b < c*α := max_lt hac (by nlinarith)
  have hp : 0 < α-1 := by linarith
  have hlarge : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ b*(n : ℝ)^(α-1) :=
    (((tendsto_rpow_atTop hp).comp tendsto_natCast_atTop_atTop).const_mul_atTop hb0).eventually_ge_atTop _
  obtain ⟨M,hM⟩ := eventually_atTop.mp hlarge
  have hQ : 2 ≤ Fintype.card W := by
    obtain ⟨x,y,hxy⟩ := hEdge
    exact Fintype.one_lt_card_iff.mpr ⟨x,y,hxy.ne⟩
  filter_upwards [nearby_joint_witnesses H hH hEdge ha ha2 hc hbc hd hε h (max N M) D] with k hk
  obtain ⟨U,hU,J,hnNM,hnlo,hnhi,hf,he,hD,hMin,hFold,hBack,hMerge,hMissing⟩ := hk
  have hab : a*(Fintype.card U : ℝ)^(α-1) ≤ b*(Fintype.card U : ℝ)^(α-1) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hBack1 : (1 : ℝ) < (extremalNumber (Fintype.card U) H : ℝ)-
      (extremalNumber (Fintype.card U-1) H : ℝ) :=
    (hM (Fintype.card U) ((le_max_right N M).trans hnNM)).trans_lt hBack
  refine ⟨U,hU,J,(le_max_left N M).trans hnNM,hnlo,hnhi,hf,he,hD,
    fun v => hab.trans (hMin v),hFold,hab.trans_lt hBack,?_,hMissing,?_⟩
  · exact fun u v huv hn hsmall => hMerge u v huv hn (hsmall.trans hab)
  · exact fun _ _ huv => every_edge_on_short_odd_cycle hH hQ hRest hf he hBack1 huv

#print axioms nearby_joint_odd_witnesses
end Erdos713JointOddCycleWitnesses
