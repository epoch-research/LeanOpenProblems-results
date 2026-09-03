import Submission.NearCompleteCrossingAbsorption
import Submission.SplitCorePartners
import Submission.NearCompleteCarrierSupport
import Submission.NearCompleteContiguousAbsorption

/-! Unbounded-length absorption for a complete-minus-one-edge even cycle
core with at most one intrinsic outside excursion among its carriers. -/
namespace Erdos583NearCompleteOneExcursionAbsorptionDevelopment
open SimpleGraph Erdos583Work
open Erdos583PathCoreIntervalsDevelopment Erdos583OneGapArithmeticDevelopment
open Erdos583NearCompleteCrossingAbsorptionDevelopment Erdos583SplitCorePartnersDevelopment
open Erdos583NearCompleteCarrierSupportDevelopment Erdos583NearCompleteContiguousAbsorptionDevelopment
open scoped Classical
set_option maxHeartbeats 2000000
set_option Elab.async false

lemma near_complete_one_excursion_absorption {V : Type*} [Fintype V] {G : SimpleGraph V}
    {t : ℕ} {r : V} (C : G.Walk r r) (hC : C.IsCycle)
    (a b : Fin t → V) (p : ∀ i, G.Walk (a i) (b i))
    (hp : ∀ i, (p i).IsPath)
    (hd : Pairwise (fun i j ↦ Disjoint (p i).toSubgraph.edgeSet (p j).toSubgraph.edgeSet))
    (hCp : ∀ i, Disjoint C.toSubgraph.edgeSet (p i).toSubgraph.edgeSet)
    (hc : C.toSubgraph.edgeSet ∪ (⋃ i, (p i).toSubgraph.edgeSet)=G.edgeSet)
    (hlen : C.length=2*t+2) (u v : C.toSubgraph.verts) (huv : u ≠ v)
    (hnear : G.induce C.toSubgraph.verts=
      (⊤ : SimpleGraph C.toSubgraph.verts).deleteEdges {s(u,v)})
    (j : Fin t)
    (hj : (coreEdges (p j) C.toSubgraph.verts).ncard+2=
      (coreVerts (p j) C.toSubgraph.verts).ncard)
    (hother : ∀ i, i ≠ j → (coreEdges (p i) C.toSubgraph.verts).ncard+1=
      (coreVerts (p i) C.toSubgraph.verts).ncard) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ t+1 := by
  classical
  have hsize := near_complete_carriers_two_core_vertices C hC a b p hp hc hlen u v huv hnear
  have hS (i : Fin t) : (coreVerts (p i) C.toSubgraph.verts).Nonempty :=
    (Set.ncard_pos (Set.toFinite _)).mp (by have := hsize i; omega)
  obtain ⟨z,hz,A,B,hform,hAS,hBS,hAc,hBc⟩ := one_gap_split (p j) (hp j) C.toSubgraph.verts hj
  let R {x y : V} (P : G.Walk x y) :=
    (coreVerts P C.toSubgraph.verts).Nonempty ∧
    (coreEdges P C.toSubgraph.verts).ncard+1=(coreVerts P C.toSubgraph.verts).ncard
  obtain ⟨x,y,q,hq,hqd,hCq,hqc,hRq,hcap,hpair⟩ :=
    split_core_family_with_partners a b p hp hd C.toSubgraph.edgeSet hCp C.toSubgraph.verts hsize
      R j hz A B hform ⟨hAS,hAc⟩ ⟨hBS,hBc⟩ (fun i hij ↦ ⟨hS i,hother i hij⟩)
  exact contiguous_near_complete_crossing_absorption C hC x y q hq
    (fun i ↦ (hRq i).1) (fun i ↦ (hRq i).2) hqd hCq (by rw [hqc]; exact hc)
    hlen u v huv hnear hcap hpair

lemma near_complete_at_most_one_excursion_absorption {V : Type*} [Fintype V] {G : SimpleGraph V}
    {t : ℕ} {r : V} (C : G.Walk r r) (hC : C.IsCycle)
    (a b : Fin t → V) (p : ∀ i, G.Walk (a i) (b i))
    (hp : ∀ i, (p i).IsPath)
    (hd : Pairwise (fun i j ↦ Disjoint (p i).toSubgraph.edgeSet (p j).toSubgraph.edgeSet))
    (hCp : ∀ i, Disjoint C.toSubgraph.edgeSet (p i).toSubgraph.edgeSet)
    (hc : C.toSubgraph.edgeSet ∪ (⋃ i, (p i).toSubgraph.edgeSet)=G.edgeSet)
    (hlen : C.length=2*t+2) (u v : C.toSubgraph.verts) (huv : u ≠ v)
    (hnear : G.induce C.toSubgraph.verts=
      (⊤ : SimpleGraph C.toSubgraph.verts).deleteEdges {s(u,v)})
    (hgap : (∑ i, ((coreVerts (p i) C.toSubgraph.verts).ncard-1-
      (coreEdges (p i) C.toSubgraph.verts).ncard)) ≤ 1) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ t+1 := by
  classical
  have hsize := near_complete_carriers_two_core_vertices C hC a b p hp hc hlen u v huv hnear
  have hS (i : Fin t) : (coreVerts (p i) C.toSubgraph.verts).Nonempty :=
    (Set.ncard_pos (Set.toFinite _)).mp (by have := hsize i; omega)
  have hbound (i : Fin t) := core_edge_bound (p i) (hp i) C.toSubgraph.verts (hS i)
  let g (i : Fin t) := (coreVerts (p i) C.toSubgraph.verts).ncard-1-
    (coreEdges (p i) C.toSubgraph.verts).ncard
  change (∑ i, g i) ≤ 1 at hgap
  by_cases hzero : (∑ i, g i)=0
  · have hz (i : Fin t) : (coreEdges (p i) C.toSubgraph.verts).ncard+1=
        (coreVerts (p i) C.toSubgraph.verts).ncard := by
      have hg : g i ≤ ∑ j, g j := Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
      have hb := hbound i
      rw [hzero] at hg
      dsimp only [g] at hg
      omega
    exact contiguous_near_complete_cycle_absorption C hC a b p hp hS hz hd hCp hc hlen u v huv hnear
  · have hone : (∑ i, g i)=1 := by omega
    obtain ⟨j,hj,hother⟩ := sum_one_unique g hone
    apply near_complete_one_excursion_absorption C hC a b p hp hd hCp hc hlen u v huv hnear j
    · have hb := hbound j
      dsimp only [g] at hj
      omega
    · intro i hij
      have ho := hother i hij
      have hb := hbound i
      dsimp only [g] at ho
      omega

end Erdos583NearCompleteOneExcursionAbsorptionDevelopment
