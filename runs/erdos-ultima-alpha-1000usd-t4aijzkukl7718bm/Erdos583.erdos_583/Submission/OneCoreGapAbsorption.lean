import Submission.CycleOneCoreGap
import Submission.CoreIntervalSplicing
import Submission.SplitPathFamily

/-! Absorb a cycle at arbitrary length when the aggregate full-core
edge deficit of its path carriers is at most one. -/
namespace Erdos583OneCoreGapAbsorptionDevelopment
open SimpleGraph Erdos583Work
open Erdos583PathCoreIntervalsDevelopment Erdos583OneGapArithmeticDevelopment
open Erdos583CycleOneCoreGapDevelopment Erdos583CoreIntervalSplicingDevelopment
open Erdos583SplitPathFamilyDevelopment
open scoped Classical
set_option maxHeartbeats 1800000
set_option Elab.async false

lemma one_core_gap_absorption {V : Type*} [Fintype V] {G : SimpleGraph V}
    {t : ℕ} {r : V} (C : G.Walk r r) (hC : C.IsCycle)
    (a b : Fin t → V) (p : ∀ i, G.Walk (a i) (b i))
    (hp : ∀ i, (p i).IsPath)
    (hS : ∀ i, (coreVerts (p i) C.toSubgraph.verts).Nonempty)
    (hd : Pairwise (fun i j ↦ Disjoint (p i).toSubgraph.edgeSet (p j).toSubgraph.edgeSet))
    (hCp : ∀ i, Disjoint C.toSubgraph.edgeSet (p i).toSubgraph.edgeSet)
    (hc : C.toSubgraph.edgeSet ∪ (⋃ i, (p i).toSubgraph.edgeSet)=G.edgeSet)
    (hdense : C.length ≤ 2*t+2)
    (hgap : (∑ i, (C.length-1-(coreEdges (p i) C.toSubgraph.verts).ncard)) ≤ 1) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ t+1 := by
  classical
  obtain ⟨hlen,hgap1,htop⟩ := one_core_gap_forces_clique C hC a b p hp hS hd hCp hc hdense hgap
  have hspan := spanning_of_complete_core C hC a b p hp hc hlen htop
  have hv (i : Fin t) : (coreVerts (p i) C.toSubgraph.verts).ncard=C.length := by
    rw [hspan,Walk.verts_toSubgraph,cycle_support_ncard hC]
  have he (i : Fin t) : (coreEdges (p i) C.toSubgraph.verts).ncard+1 ≤ C.length := by
    simpa only [hv] using core_edge_bound (p i) (hp i) C.toSubgraph.verts (hS i)
  obtain ⟨j,hj,hother⟩ := sum_one_unique
    (fun i ↦ C.length-1-(coreEdges (p i) C.toSubgraph.verts).ncard) hgap1
  have hjcount : (coreEdges (p j) C.toSubgraph.verts).ncard+2=
      (coreVerts (p j) C.toSubgraph.verts).ncard := by
    rw [hv]
    have hb := he j
    have h3 := hC.three_le_length
    omega
  obtain ⟨z,_,A,B,hform,hAS,hBS,hAc,hBc⟩ := one_gap_split (p j) (hp j) C.toSubgraph.verts hjcount
  let R {u v : V} (P : G.Walk u v) :=
    (coreVerts P C.toSubgraph.verts).Nonempty ∧
    (coreEdges P C.toSubgraph.verts).ncard+1=(coreVerts P C.toSubgraph.verts).ncard
  have hR (i : Fin t) (hij : i ≠ j) : R (p i) := by
    refine ⟨hS i,?_⟩
    rw [hv]
    have hh := hother i hij
    have hb := he i
    omega
  obtain ⟨x,y,q,hq,hqd,hCq,hqc,hRq⟩ := split_path_family a b p hp hd
    C.toSubgraph.edgeSet hCp R j A B hform ⟨hAS,hAc⟩ ⟨hBS,hBc⟩ hR
  exact contiguous_clique_cycle_absorption C hC x y q hq
    (fun i ↦ (hRq i).1) (fun i ↦ (hRq i).2) hqd hCq
    (by rw [hqc]; exact hc) (by omega) htop

end Erdos583OneCoreGapAbsorptionDevelopment
