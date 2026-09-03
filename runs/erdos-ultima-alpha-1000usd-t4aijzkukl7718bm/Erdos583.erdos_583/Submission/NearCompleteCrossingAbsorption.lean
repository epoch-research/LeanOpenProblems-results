import Submission.NearCompleteCrossingSplicing
import Submission.CrossingArmSupport

/-! Absorption for contiguous near-complete core intervals, including a nil
interval whose carrier came from an outside split of a simple path. -/
namespace Erdos583NearCompleteCrossingAbsorptionDevelopment
open SimpleGraph Erdos583Work
open Erdos583PathCoreIntervalsDevelopment
open Erdos583NearCompleteCrossingSplicingDevelopment Erdos583CrossingArmSupportDevelopment
open scoped Classical
set_option maxHeartbeats 2000000
set_option Elab.async false

lemma contiguous_near_complete_crossing_absorption {V : Type*} [Fintype V] {G : SimpleGraph V}
    {t : ℕ} {r : V} (C : G.Walk r r) (hC : C.IsCycle)
    (a b : Fin (t+1) → V) (p : ∀ i, G.Walk (a i) (b i))
    (hp : ∀ i, (p i).IsPath)
    (hS : ∀ i, (coreVerts (p i) C.toSubgraph.verts).Nonempty)
    (hz : ∀ i, (coreEdges (p i) C.toSubgraph.verts).ncard+1=
      (coreVerts (p i) C.toSubgraph.verts).ncard)
    (hd : Pairwise (fun i j ↦ Disjoint (p i).toSubgraph.edgeSet (p j).toSubgraph.edgeSet))
    (hCp : ∀ i, Disjoint C.toSubgraph.edgeSet (p i).toSubgraph.edgeSet)
    (hc : C.toSubgraph.edgeSet ∪ (⋃ i, (p i).toSubgraph.edgeSet)=G.edgeSet)
    (hlen : C.length=2*t+2) (u₀ v₀ : C.toSubgraph.verts) (huv₀ : u₀ ≠ v₀)
    (hnear : G.induce C.toSubgraph.verts=
      (⊤ : SimpleGraph C.toSubgraph.verts).deleteEdges {s(u₀,v₀)})
    (hcap : ∀ w ∈ C.toSubgraph.verts,
      (Finset.univ.filter fun i ↦ w ∈ (p i).support).card ≤ t)
    (hpair : ∀ i, (coreVerts (p i) C.toSubgraph.verts).ncard=1 → ∃ j z,
      i ≠ j ∧ z ∉ C.toSubgraph.verts ∧ ((b i=z ∧ a j=z) ∨ (a i=z ∧ b j=z)) ∧
      ∀ w ∈ (p i).support, w ∈ (p j).support → w=z) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ t+1 := by
  classical
  choose u v A Q B hform hQ hQv hA hB using
    fun i ↦ contiguous_of_core_count (p i) (hp i) C.toSubgraph.verts (hS i) (hz i)
  have hQS (i : Fin (t+1)) (w : V) (hw : w ∈ (Q i).support) : w ∈ C.toSubgraph.verts := by
    have hm := (Q i).mem_verts_toSubgraph.mpr hw
    rw [hQv i] at hm
    exact hm.2
  have hcard : 2*t+2=Fintype.card C.toSubgraph.verts := by
    rw [←Nat.card_eq_fintype_card,Nat.card_coe_set_eq,Walk.verts_toSubgraph,
      cycle_support_ncard hC,hlen]
  apply explicit_near_complete_crossing_splice C hC C.toSubgraph.verts rfl u v a b A Q B
    (fun i ↦ hform i ▸ hp i) hQS hA hB ?_ ?_ ?_ hcard u₀ v₀ huv₀ hnear ?_ ?_
  · simpa only [←hform] using hd
  · simpa only [←hform] using hCp
  · simpa only [←hform] using hc
  · intro w hw
    apply le_trans (Finset.card_le_card (show
      (Finset.univ.filter fun i ↦ w ∈ (Q i).support) ⊆
        (Finset.univ.filter fun i ↦ w ∈ (p i).support) from ?_)) (hcap w hw)
    intro i hi
    obtain ⟨_,hi⟩ := Finset.mem_filter.mp hi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    have hm := (Q i).mem_verts_toSubgraph.mpr hi
    rw [hQv i] at hm
    exact (p i).mem_verts_toSubgraph.mp hm.1
  · intro i hi
    have hcount : (coreVerts (p i) C.toSubgraph.verts).ncard=1 := by
      rw [←hQv i]
      exact path_card_one_of_ends_eq (Q i) (hQ i) hi
    obtain ⟨j,z,hij,hz,hends,hmeet⟩ := hpair i hcount
    refine ⟨j,hij,?_⟩
    apply core_interval_pair_arm_disjoint (A i) (Q i) (B i) (A j) (Q j) (B j)
      (hform i ▸ hp i) (hform j ▸ hp j) C.toSubgraph.verts
      (hQS i _ (Q i).start_mem_support) (hQS i _ (Q i).end_mem_support)
      (hQS j _ (Q j).start_mem_support) (hQS j _ (Q j).end_mem_support) hz hends
    simpa only [←hform] using hmeet

end Erdos583NearCompleteCrossingAbsorptionDevelopment
