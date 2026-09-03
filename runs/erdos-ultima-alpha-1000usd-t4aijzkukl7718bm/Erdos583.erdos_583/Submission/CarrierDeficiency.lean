import Submission.Work
import Submission.CarrierCount
import Submission.CarrierLength
import Submission.CarrierGroups
import Submission.OutsideCarrierBudget

/-! Incidence deficiency survives the carrier optimization. -/
namespace Erdos583CarrierDeficiencyDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery
open Erdos583CarrierCountDevelopment Erdos583CarrierLengthDevelopment
open Erdos583CarrierGroupsDevelopment Erdos583OutsideCarrierBudgetDevelopment
open scoped Classical
set_option maxHeartbeats 1800000
variable {V : Type*} {G : SimpleGraph V} {k : ℕ}

lemma touches_iff_support {a b : V} (P : G.Walk a b) (hn : ¬P.Nil) (S : Set V) :
    Touches S P.toSubgraph ↔ ∃ x ∈ S, x ∈ P.support := by
  constructor
  · rintro ⟨x,hx,y,hxy⟩
    exact ⟨x,hx,Walk.mem_support_of_adj_toSubgraph hxy⟩
  · rintro ⟨x,hx,hxp⟩
    obtain ⟨y,hy⟩ := VertexTracking.walk_vertex_has_subgraph_neighbor P hn (P.mem_verts_toSubgraph.mpr hxp)
    exact ⟨x,hx,y,hy⟩

lemma carrierCount_lt_iff (T : TrailFamily G k) (S : Set V) :
    carrierCount T S < k ↔ ∃ j, ¬Touches S (T.walk j).toSubgraph := by
  classical
  constructor
  · intro hh
    by_contra! hn
    have he : carrierCount T S=k := by simp [carrierCount,hn]
    omega
  · rintro ⟨j,hj⟩
    have hsub : (Finset.univ.filter (fun l ↦ Touches S (T.walk l).toSubgraph)) ⊂ Finset.univ := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨Finset.filter_subset _ _,?_⟩
      intro he
      have hj' : j ∈ Finset.univ.filter (fun l ↦ Touches S (T.walk l).toSubgraph) := by rw [he]; simp
      exact hj (Finset.mem_filter.mp hj').2
    have hh := Finset.card_lt_card hsub
    simpa only [Finset.card_filter,Finset.card_univ,Fintype.card_fin,carrierCount] using hh

lemma small_root_deficiency [Fintype V] (T : TrailFamily G k) (r : V)
    (hr : QuotaRooted.HasRoot T r) (hq : T.quota r ≤ 2) (hk : Fintype.card V ≤ 2*k) :
    carrierCount T {r} < k := by
  obtain ⟨j,hj⟩ := RootEnergy.exists_member_avoiding_small_quota_root T r hr hq hk
  apply (carrierCount_lt_iff T {r}).mpr
  refine ⟨j,?_⟩
  rintro ⟨x,hx,y,hxy⟩
  have he : x=r := hx
  subst x
  exact hj (Walk.mem_support_of_adj_toSubgraph hxy)

lemma five_cycle_carrierCount [Fintype V] (T : TrailFamily G k)
    (hs : T.score+1=G.edgeSet.ncard+k) (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (i : Fin k) {r : V} (C : G.Walk r r) (hC : C.IsCycle) (hfive : C.length=5)
    (hi : (T.walk i).toSubgraph=C.toSubgraph) (x : V) (hx : x ∈ C.support) :
    carrierCount T C.toSubgraph.verts=carrierCount T {x} := by
  have hn := NilSlot.max_score_nonpath_no_nil T hm ⟨i,CycleEar.cycle_member_not_path T i C hC hi⟩
  unfold carrierCount
  apply Finset.sum_congr rfl
  intro j hj
  suffices hh : Touches C.toSubgraph.verts (T.walk j).toSubgraph ↔ Touches {x} (T.walk j).toSubgraph by rw [hh]
  rw [touches_iff_support _ (hn j),touches_iff_support _ (hn j)]
  constructor
  · rintro ⟨y,hy,hyj⟩
    exact ⟨x,rfl,(PentagonIntersection.five_cycle_equal_members T hs hm i C hC hfive hi
      (C.mem_verts_toSubgraph.mp hy) hx j).mp hyj⟩
  · rintro ⟨y,hy,hyj⟩
    have he : y=x := hy
    subst y
    exact ⟨x,C.mem_verts_toSubgraph.mpr hx,hyj⟩

lemma pentagon_outside_of_preserved_root [Fintype V] (T U : TrailFamily G k)
    (r : V) (hr : QuotaRooted.HasRoot T r) (hq : T.quota r ≤ 2) (hk : Fintype.card V ≤ 2*k)
    (hs : U.score+1=G.edgeSet.ncard+k) (hm : ∀ Z : TrailFamily G k, Z.score ≤ U.score)
    (i : Fin k) (C : G.Walk r r) (hC : C.IsCycle) (hfive : C.length=5)
    (hi : (U.walk i).toSubgraph=C.toSubgraph)
    (hp : PreservesIncidence T U C.toSubgraph.verts) :
    (outsideIndices U C.toSubgraph.verts).Nonempty ∧ (carrierIndices U i C.toSubgraph.verts).card+2 ≤ k := by
  have hd := small_root_deficiency T r hr hq hk
  have he := hp r C.start_mem_verts_toSubgraph
  have hc := five_cycle_carrierCount U hs hm i C hC hfive hi r C.start_mem_support
  have hlt : carrierCount U C.toSubgraph.verts < k := by omega
  obtain ⟨j,hj⟩ := (carrierCount_lt_iff U C.toSubgraph.verts).mp hlt
  have hj' : j ∈ outsideIndices U C.toSubgraph.verts := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩
  have hnon : (outsideIndices U C.toSubgraph.verts).Nonempty := ⟨j,hj'⟩
  have hb := outside_carrier_partition U i C.toSubgraph.verts (cycle_touches U i C hC hi)
  have hpos := Finset.card_pos.mpr hnon
  exact ⟨hnon,by omega⟩

lemma exists_optimal_with_root_deficiency [Fintype V] (T : TrailFamily G k) (r : V)
    (hr : QuotaRooted.HasRoot T r) (hq : T.quota r ≤ 2) (hk : Fintype.card V ≤ 2*k)
    (i : Fin k) (C : G.Walk r r) (hi : (T.walk i).toSubgraph=C.toSubgraph) :
    ∃ U : TrailFamily G k, U.score=T.score ∧ (U.walk i).toSubgraph=C.toSubgraph ∧
      PreservesIncidence T U C.toSubgraph.verts ∧ carrierCount U {r} < k ∧
      (∀ Z : TrailFamily G k, Z.score=U.score → (Z.walk i).toSubgraph=C.toSubgraph →
        PreservesIncidence U Z C.toSubgraph.verts →
        carrierCount Z C.toSubgraph.verts ≤ carrierCount U C.toSubgraph.verts) ∧
      (∀ Z : TrailFamily G k, Z.score=U.score → (Z.walk i).toSubgraph=C.toSubgraph →
        PreservesIncidence U Z C.toSubgraph.verts →
        carrierCount Z C.toSubgraph.verts=carrierCount U C.toSubgraph.verts →
        carrierLength U C.toSubgraph.verts ≤ carrierLength Z C.toSubgraph.verts) := by
  obtain ⟨U,hUs,hUi,hUp,hUmax,hUmin⟩ := exists_shortest_maximum_carriers T i C hi
  have hh := small_root_deficiency T r hr hq hk
  have he := hUp r C.start_mem_verts_toSubgraph
  exact ⟨U,hUs,hUi,hUp,by omega,hUmax,hUmin⟩

end Erdos583CarrierDeficiencyDevelopment
