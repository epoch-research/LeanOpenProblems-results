import Submission.OneTailCycleVisits
import Submission.CriticalRootCarrier

/-! The four-visit restriction holds in every optimal remainder partition.
In the odd-order degree-five pentagon branch the remainder root is not a
cut vertex. These are necessary conditions, not a proof of the conjecture. -/
namespace Erdos583OneTailRemainderVisitsDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery Erdos583Work.LollipopEar
open Erdos583Work.MemberExpansion Erdos583Work.MemberNormalExpansion Erdos583Work.GroupActivation
open Erdos583UnifiedMinimalDefectDevelopment Erdos583NormalRemainderCriticalDevelopment
open Erdos583UniversalNormalEndpointsDevelopment Erdos583CriticalRootCarrierDevelopment
open Erdos583OneTailCycleBoundaryDevelopment Erdos583OneTailCycleVisitsDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma normal_member_realization (F : MinimalFailure) (D : OptimizedDefect F.graph)
    (T : TrailFamily (remainder F D) (normalBudget F D)) (hp : ∀ j, (T.walk j).IsPath)
    (i : Fin (normalBudget F D)) :
    ∃ U : TrailFamily F.graph (budget F.order), ∃ j, ∃ M : RootedCycleRep U D.root,
      U.score+1=F.graph.edgeSet.ncard+budget F.order ∧
      (∀ W : TrailFamily F.graph (budget F.order), W.score ≤ U.score) ∧
      M.cycle=D.rep.cycle ∧ M.tail.length=D.rep.tail.length ∧ M.index ≠ j ∧
      (∀ v, v ∈ (U.walk j).support ↔ v ∈ (T.walk i).support) := by
  obtain ⟨E,hE,hEc,hparts⟩ := CutVertexReduction.path_family_partition_tracked T hp
  have hEq : E.card=normalBudget F D := (normal_partition_lower_bound F D E hE).antisymm' hEc
  obtain ⟨U,hUs,hrest,_,_,hUparts⟩ := replace_path_group_tracked D.family (normalIndices F D)
    (fun j hj ↦ (D.family.one_defect_other_paths D.score D.rep.index D.rep.member_not_path).2
      j (Finset.mem_erase.mp hj).1) E hE hEq
  have hkeep := hrest D.rep.index (by simp [normalIndices])
  let M : RootedCycleRep U D.root :=
    { D.rep with
      start_eq := hkeep.1.trans D.rep.start_eq
      finish_eq := hkeep.2.1.trans D.rep.finish_eq
      subgraph := hkeep.2.2.trans D.rep.subgraph }
  obtain ⟨j,hj,hUj⟩ := hUparts (T.walk i).toSubgraph (hparts i)
  let Q := (T.walk i).mapLe (selectedGraph_le D.family (normalIndices F D))
  have hQe : Q.toSubgraph=(T.walk i).toSubgraph.map
      (Hom.ofLE (selectedGraph_le D.family (normalIndices F D))) := by
    simp only [Q,Walk.mapLe,Walk.toSubgraph_map]
  have hUQ : (U.walk j).toSubgraph=Q.toSubgraph := hUj.trans hQe.symm
  have hmem : ∀ v, v ∈ (U.walk j).support ↔ v ∈ (T.walk i).support := by
    intro v
    rw [←Walk.mem_verts_toSubgraph,hUQ,Walk.mem_verts_toSubgraph]
    simp only [Q,Walk.support_mapLe_eq_support]
  exact ⟨U,j,M,by rw [hUs]; exact D.score,
    (fun W ↦ by rw [hUs]; exact D.maximum W),rfl,rfl,(Finset.mem_erase.mp hj).1.symm,hmem⟩

lemma normal_one_tail_four_cycle_visits (F : MinimalFailure) (D : OptimizedDefect F.graph)
    (hl : D.rep.tail.length=1)
    (T : TrailFamily (remainder F D) (normalBudget F D)) (hp : ∀ j, (T.walk j).IsPath)
    (i : Fin (normalBudget F D)) (hr : D.root ∉ (T.walk i).support)
    (hhit : ∃ v ∈ (T.walk i).support, v ∈ D.rep.cycle.support) :
    4 ≤ (D.rep.cycle.toSubgraph.verts ∩ (T.walk i).toSubgraph.verts).ncard := by
  obtain ⟨U,j,M,hs,hm,hC,hlength,hij,hmem⟩ := normal_member_realization F D T hp i
  have hr' : D.root ∉ (U.walk j).support := fun h ↦ hr ((hmem _).mp h)
  have hhit' : ∃ v ∈ (U.walk j).support, v ∈ M.cycle.support := by
    obtain ⟨v,hv,hvC⟩ := hhit
    exact ⟨v,(hmem _).mpr hv,by rwa [hC]⟩
  have hh := maximum_one_tail_four_cycle_visits U hs hm D.root M (hlength.trans hl) j hij hr' hhit'
  have he : (U.walk j).toSubgraph.verts=(T.walk i).toSubgraph.verts := by
    ext v
    simpa only [Walk.mem_verts_toSubgraph] using hmem v
  rwa [hC,he] at hh

lemma normal_one_tail_pentagon_contains (F : MinimalFailure) (D : OptimizedDefect F.graph)
    (hl : D.rep.tail.length=1) (hc : D.rep.cycle.length=5)
    (T : TrailFamily (remainder F D) (normalBudget F D)) (hp : ∀ j, (T.walk j).IsPath)
    (i : Fin (normalBudget F D)) (hr : D.root ∉ (T.walk i).support)
    (hhit : ∃ v ∈ (T.walk i).support, v ∈ D.rep.cycle.support) :
    ∀ v ∈ D.rep.cycle.support, v ≠ D.root → v ∈ (T.walk i).support := by
  obtain ⟨U,j,M,hs,hm,hC,hlength,hij,hmem⟩ := normal_member_realization F D T hp i
  have hr' : D.root ∉ (U.walk j).support := fun h ↦ hr ((hmem _).mp h)
  have hhit' : ∃ v ∈ (U.walk j).support, v ∈ M.cycle.support := by
    obtain ⟨v,hv,hvC⟩ := hhit
    exact ⟨v,(hmem _).mpr hv,by rwa [hC]⟩
  intro v hvC hvr
  apply (hmem v).mp
  exact maximum_one_tail_pentagon_avoider_contains U hs hm D.root M
    (hlength.trans hl) (by rwa [hC]) j hij hr' hhit' v (by rwa [hC]) hvr

lemma odd_one_tail_degree_five_avoider (F : MinimalFailure) (D : OptimizedDefect F.graph)
    (ho : Odd F.order) (hl : D.rep.tail.length=1)
    (hd : Nat.card (F.graph.neighborSet D.root) ≤ 5) :
    ∃ j, D.rep.index ≠ j ∧ D.root ∉ (D.family.walk j).support ∧
      D.rep.cycle.snd ∈ (D.family.walk j).support := by
  have hq := Erdos583RootEndpointTailCapacityDevelopment.minimum_one_edge_tail_root_quota_one
    D.family D.score D.maximum D.root D.rep D.cycle_minimum hl
  have hsne : D.rep.cycle.snd ≠ D.root := (D.rep.cycle.adj_snd D.rep.isCycle.not_nil).ne.symm
  have hlow := DegreeFourReduction.min_degree_five_of_odd_failure
    F.smaller ho F.connected F.failure D.rep.cycle.snd
  by_contra hn
  have hdom : ∀ j, D.rep.cycle.snd ∈ (D.family.walk j).support →
      D.root ∈ (D.family.walk j).support := by
    intro j hj
    by_contra hr
    have hij : D.rep.index ≠ j := by
      intro he
      apply hr
      rw [←he,←Walk.mem_verts_toSubgraph,D.rep.subgraph,Walk.mem_verts_toSubgraph,
        Walk.mem_support_append_iff]
      exact Or.inl D.rep.cycle.start_mem_support
    exact hn ⟨j,hij,hr,hj⟩
  have hb := Erdos583ShortTriangleIncidenceDevelopment.rooted_support_degree_dominance
    D.family D.root D.score D.rep.hasRoot hsne hdom
  omega

lemma path_reachable_avoiding {V : Type*} {H : SimpleGraph V} {a b r x y : V}
    (P : H.Walk a b) (hr : r ∉ P.support) (hx : x ∈ P.support) (hy : y ∈ P.support) :
    (BridgeGlue.within H ({r}ᶜ : Set V)).Reachable x y := by
  let f : P.toSubgraph.coe →g BridgeGlue.within H ({r}ᶜ : Set V) :=
    { toFun := Subtype.val
      map_rel' := by
        intro u v huv
        refine ⟨P.toSubgraph.adj_sub huv,?_,?_⟩
        · intro he
          exact hr (he ▸ P.mem_verts_toSubgraph.mp u.property)
        · intro he
          exact hr (he ▸ P.mem_verts_toSubgraph.mp v.property) }
  exact (P.toSubgraph_connected ⟨x,P.mem_verts_toSubgraph.mpr hx⟩
    ⟨y,P.mem_verts_toSubgraph.mpr hy⟩).map f

lemma normal_one_tail_off_root_edge (F : MinimalFailure) (D : OptimizedDefect F.graph)
    (hl : D.rep.tail.length=1) {x y : Fin F.order} (hxr : x ≠ D.root) (hyr : y ≠ D.root)
    (hxy : F.graph.Adj x y) :
    (remainder F D).Adj x y ∨ D.rep.cycle.toSubgraph.Adj x y := by
  by_cases hH : (remainder F D).Adj x y
  · exact Or.inl hH
  right
  have he : s(x,y) ∈ (D.family.walk D.rep.index).toSubgraph.edgeSet := by
    by_contra hn
    apply hH
    change (selectedGraph D.family (Finset.univ.erase D.rep.index)).Adj x y
    rw [CubicRemainder.selected_erase_eq_delete,deleteEdges_adj]
    exact ⟨hxy,hn⟩
  rw [one_tail_anchor_edges D.family D.root D.rep hl] at he
  rcases he with he|he
  · rcases Sym2.eq_iff.mp he with ⟨hx,_⟩|⟨_,hy⟩
    · exact (hxr hx).elim
    · exact (hyr hy).elim
  · exact he

lemma normal_delete_root_connected_of_carrier (F : MinimalFailure) (D : OptimizedDefect F.graph)
    (ho : Odd F.order) (hl : D.rep.tail.length=1)
    {a b : Fin F.order} (P : (remainder F D).Walk a b)
    (hr : D.root ∉ P.support)
    (hC : ∀ v ∈ D.rep.cycle.support, v ≠ D.root → v ∈ P.support) :
    ((remainder F D).induce ({D.root}ᶜ : Set (Fin F.order))).Connected := by
  let S : Set (Fin F.order) := {D.root}ᶜ
  have hG : (F.graph.induce S).Connected := CutVertexReduction.delete_vertex_connected_of_odd_failure
    F.smaller ho F.connected F.failure D.root
  letI : Nonempty S := hG.nonempty
  have hstep : ∀ x y : S, (F.graph.induce S).Adj x y →
      ((remainder F D).induce S).Reachable x y := by
    intro x y hxy
    rcases normal_one_tail_off_root_edge F D hl x.property y.property hxy with hH|hCxy
    · exact (show ((remainder F D).induce S).Adj x y from hH).reachable
    · apply DegreeThreeReduction.within_reachable_induce
      exact path_reachable_avoiding P hr
        (hC x.val (Walk.mem_support_of_adj_toSubgraph hCxy) x.property)
        (hC y.val (Walk.mem_support_of_adj_toSubgraph hCxy.symm) y.property)
  refine ⟨fun x y ↦ ?_⟩
  exact reachable_map_to_reachable id hstep (hG.preconnected x y)

lemma odd_one_tail_degree_five_pentagon_root_not_cut (F : MinimalFailure) (D : OptimizedDefect F.graph)
    (ho : Odd F.order) (hl : D.rep.tail.length=1) (hc : D.rep.cycle.length=5)
    (hd : Nat.card (F.graph.neighborSet D.root) ≤ 5) :
    ((remainder F D).induce ({D.root}ᶜ : Set (Fin F.order))).Connected := by
  obtain ⟨j,hij,hr,hj⟩ := odd_one_tail_degree_five_avoider F D ho hl hd
  have hm : ∀ e ∈ (D.family.walk j).edges, e ∈ (remainder F D).edgeSet := by
    intro e he
    apply (selected_edge_iff D.family (normalIndices F D) e).mpr
    exact ⟨j,Finset.mem_erase.mpr ⟨hij.symm,Finset.mem_univ _⟩,
      (D.family.walk j).mem_edges_toSubgraph.mpr he⟩
  let P := (D.family.walk j).transfer (remainder F D) hm
  have hC := maximum_one_tail_pentagon_avoider_contains D.family D.score D.maximum
    D.root D.rep hl hc j hij hr ⟨D.rep.cycle.snd,hj,D.rep.cycle.getVert_mem_support 1⟩
  apply normal_delete_root_connected_of_carrier F D ho hl P
  · simpa only [P,Walk.support_transfer] using hr
  · simpa only [P,Walk.support_transfer] using hC

end Erdos583OneTailRemainderVisitsDevelopment
