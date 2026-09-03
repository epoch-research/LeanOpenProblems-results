import Submission.UnifiedMinimalDefect
import Submission.CycleNeighborClosure

/-! Fresh cycle shortcuts away from the root, with an arbitrary attached tail retained. -/
namespace Erdos583RootedCycleNeighborClosureDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.LollipopEar Erdos583Work.CycleEar
open Erdos583CycleNeighborClosureDevelopment
open scoped Classical
set_option maxHeartbeats 2400000
set_option Elab.async false

lemma rooted_cycle_avoider_no_chord {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (a : V) (L : RootedCycleRep T a)
    (hmin : ∀ W : TrailFamily G k, ∀ M : RootedCycleRep W a,
      W.score=T.score → (∀ z, W.quota z=T.quota z) → L.cycle.length ≤ M.cycle.length)
    (j : Fin k) (hij : L.index ≠ j) {r u v : V} (hra : r ≠ a) (hru : L.cycle.toSubgraph.Adj r u) (hrv : L.cycle.toSubgraph.Adj r v) (huv : u ≠ v)
    (hrP : r ∉ (T.walk j).support) : s(u,v) ∉ (T.walk j).edges := by
  intro he
  have hrC := Walk.mem_support_of_adj_toSubgraph hru
  let D := L.cycle.rotate hrC
  have hD : D.IsCycle := L.isCycle.rotate hrC
  obtain ⟨x,y,hrx,hyr,R,hform⟩ := cycle_two_spokes D hD
  have hCf : (Walk.cons hrx (R.concat hyr)).IsCycle := hform ▸ hD
  have hDC : (Walk.cons hrx (R.concat hyr)).toSubgraph=L.cycle.toSubgraph := by
    rw [←hform]
    exact L.cycle.toSubgraph_rotate hrC
  have haC : a ∈ (Walk.cons hrx (R.concat hyr)).support := by
    rw [←Walk.mem_verts_toSubgraph,hDC,Walk.mem_verts_toSubgraph]
    exact L.cycle.start_mem_support
  have haR : a ∈ R.support := by
    simpa only [Walk.support_cons,Walk.support_concat,List.concat_eq_append,List.mem_cons,
      List.mem_append,List.mem_singleton,List.not_mem_nil,hra.symm,false_or,or_false] using haC
  have hxC : L.cycle.toSubgraph.Adj r x := by
    rw [←L.cycle.toSubgraph_rotate hrC]
    change D.toSubgraph.Adj r x
    rw [hform]
    change s(r,x) ∈ (Walk.cons hrx (R.concat hyr)).toSubgraph.edgeSet
    rw [Walk.mem_edges_toSubgraph]
    simp
  have hyC : L.cycle.toSubgraph.Adj r y := by
    apply Subgraph.Adj.symm
    rw [←L.cycle.toSubgraph_rotate hrC]
    change D.toSubgraph.Adj y r
    rw [hform]
    change s(y,r) ∈ (Walk.cons hrx (R.concat hyr)).toSubgraph.edgeSet
    rw [Walk.mem_edges_toSubgraph]
    simp [Walk.concat_eq_append]
  have hRp : R.IsPath := ((Walk.cons_isCycle_iff _ _).mp hCf).1.of_append_left
  have hxy : x ≠ y := by
    intro heq
    subst y
    have hnil := (Walk.isPath_iff_eq_nil R).mp hRp
    have hl := hCf.three_le_length
    simp only [hnil,Walk.length_cons,Walk.length_concat,Walk.length_nil] at hl
    omega
  have hN := cycle_neighbor_pair L.cycle L.isCycle hru hrv huv
  have hx : x ∈ ({u,v} : Set V) := hN ▸ hxC
  have hy : y ∈ ({u,v} : Set V) := hN ▸ hyC
  have hpair : s(x,y)=s(u,v) := by
    rcases hx with rfl|rfl <;> rcases hy with rfl|rfl
    · exact (hxy rfl).elim
    · rfl
    · exact Sym2.eq_swap
    · exact (hxy rfl).elim
  have hedge : s(x,y) ∈ (T.walk j).edges := hpair.symm ▸ he
  have hxyG : G.Adj x y := (T.walk j).edges_subset_edgeSet hedge
  exact L.no_removable_ear T a hmin j hij hrx hyr R hCf hDC haR
    ((T.one_defect_other_paths hs L.index L.member_not_path).2 j hij.symm)
    hxyG hedge hrP

end Erdos583RootedCycleNeighborClosureDevelopment
