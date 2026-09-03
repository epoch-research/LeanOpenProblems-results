import Submission.GreedyBatchState
import Submission.GreedyMixedCommonTails

/-! Common-neighbor transport for the conservative batch. Tentative R need
not be independent, so ordinary greedy-residual identities are not assumed. -/
namespace Erdos773.GreedyBatchCommonStep
open Finset GreedyBatchState RegularizationCommonNeighbors GreedyCommonNeighbors
open GreedyMixedCommonTails
set_option maxHeartbeats 3000000
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

lemma neighbor_witness (H : Finset (Finset α)) (R : Finset α) (x y : α) (hxy : x≠y)
    (z : α) (hz : z∈both (next H R) (next H R) x y) :
    ∃ i∈patterns H x y, i.2.1=z ∧ witness x y i⊆R := by
  obtain ⟨hx,hy⟩ := mem_both.mp hz
  have hxQ := next_subset hx.2 (by simp : x∈({x,z}:Finset α))
  have hyQ := next_subset hy.2 (by simp : y∈({y,z}:Finset α))
  obtain ⟨e,he,heq⟩ := mem_image.mp hx.2
  obtain ⟨f,hf,hfq⟩ := mem_image.mp hy.2
  have hxe : x∈e := (mem_sdiff.mp (heq.symm ▸ (by simp : x∈({x,z}:Finset α)))).1
  have hyf : y∈f := (mem_sdiff.mp (hfq.symm ▸ (by simp : y∈({y,z}:Finset α)))).1
  have hze : z∈e := (mem_sdiff.mp (heq.symm ▸ (by simp : z∈({x,z}:Finset α)))).1
  have hzf : z∈f := (mem_sdiff.mp (hfq.symm ▸ (by simp : z∈({y,z}:Finset α)))).1
  have hye : y∉e := by
    intro hy'
    have hm : y∈({x,z}:Finset α) := heq ▸ mem_sdiff.mpr ⟨hy',(mem_carrier.mp hyQ).1⟩
    simp only [mem_insert,mem_singleton] at hm
    exact hm.elim hxy.symm hy.1
  have hxf : x∉f := by
    intro hx'
    have hm : x∈({y,z}:Finset α) := hfq ▸ mem_sdiff.mpr ⟨hx',(mem_carrier.mp hxQ).1⟩
    simp only [mem_insert,mem_singleton] at hm
    exact hm.elim hxy hx.1
  refine ⟨(e,z,f),mem_patterns.mpr ⟨(mem_filter.mp he).1,(mem_filter.mp hf).1,
    hxe,hyf,hze,hzf,hx.1.symm,hy.1.symm,hye,hxf⟩,rfl,?_⟩
  intro a ha
  by_contra haR
  rcases mem_union.mp ha with ha | ha
  · exact (mem_sdiff.mp ha).2 (heq ▸ mem_sdiff.mpr ⟨(mem_sdiff.mp ha).1,haR⟩)
  · exact (mem_sdiff.mp ha).2 (hfq ▸ mem_sdiff.mpr ⟨(mem_sdiff.mp ha).1,haR⟩)

lemma common_le_cost (H : Finset (Finset α)) (R : Finset α) (x y : α) (hxy : x≠y) :
    common (next H R) x y≤patternCost H x y R := by
  have hs : both (next H R) (next H R) x y⊆
      ((patterns H x y).filter (fun i => witness x y i⊆R)).image (fun i => i.2.1) := by
    intro z hz
    obtain ⟨i,hi,hiz,hR⟩ := neighbor_witness H R x y hxy z hz
    exact mem_image.mpr ⟨i,mem_filter.mpr ⟨hi,hR⟩,hiz⟩
  exact (card_le_card hs).trans card_image_le

/-- All positive support sizes are retained; old graph common neighbors
are a deterministic starting term. -/
theorem common_step (H : Finset (Finset α)) (R : Finset α)
    (hH : ∀ e∈H, e.card≤4) (x y : α) (hxy : x≠y) :
    common (next H R) x y≤common H x y+∑ r∈Icc 1 4, selectedCost H x y r R := by
  have hh := (common_le_cost H R x y hxy).trans_eq (cost_decomposition hH x y R)
  exact hh.trans (Nat.add_le_add_right (zero_le_initial_common H x y) _)

#print axioms neighbor_witness
#print axioms common_le_cost
#print axioms common_step
end
end Erdos773.GreedyBatchCommonStep
