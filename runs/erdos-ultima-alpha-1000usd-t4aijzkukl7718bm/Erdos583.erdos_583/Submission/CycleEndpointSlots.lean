import Submission.Work

/-! Counting endpoint slots at vertices common to all members of a trail family. -/
namespace Erdos583CycleEndpointSlotsDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaRooted Erdos583Work.QuotaSurgery
open scoped Classical
set_option maxHeartbeats 1600000

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}

/-- At the vertex budget, a vertex of a whole cycle that occurs in every
member is an endpoint of a member other than that cycle. No maximality
hypothesis is required. -/
lemma common_cycle_vertex_other_endpoint (T : TrailFamily G k)
    (hk : Fintype.card V ≤ 2*k) (i : Fin k) {r v : V}
    (C : G.Walk r r) (hc : C.IsCycle)
    (hi : (T.walk i).toSubgraph=C.toSubgraph) (hv : v ∈ C.support)
    (hall : ∀ j, v ∈ (T.walk j).support) :
    ∃ j : Fin k, j ≠ i ∧ (v=T.start j ∨ v=T.finish j) := by
  classical
  by_contra! hn
  let D := C.rotate hv
  have hD : D.IsCycle := hc.rotate hv
  have hDC : D.toSubgraph=C.toSubgraph := C.toSubgraph_rotate hv
  obtain ⟨U,_,ha,hb,hparts,hq⟩ := replace_one_general T i D hD.isTrail (hDC.trans hi.symm)
  have hroot : HasRoot U v := by
    cases hform : D with
    | nil => exact (hD.not_nil (hform ▸ Walk.Nil.nil)).elim
    | @cons _ w _ h q =>
      exact hasRoot_of_rep U i ha hb h q
        ((hparts i).trans (hi.trans (hDC.symm.trans (congrArg Walk.toSubgraph hform))))
        (hform ▸ hD.isTrail) q.end_mem_support
  have hTq : T.quota v=(if T.start i=v then 1 else 0)+(if T.finish i=v then 1 else 0) := by
    rw [quota_eq_sum_endpoints,Finset.sum_eq_single i]
    · intro j _ hji
      obtain ⟨hja,hjb⟩ := hn j hji
      simp [hja.symm,hjb.symm]
    · simp
  have hUq : U.quota v=2 := by
    have hh := hq v
    simp only [eq_self,ite_true] at hh
    omega
  obtain ⟨j,hj⟩ := RootEnergy.exists_member_avoiding_small_quota_root U v hroot (by omega) hk
  apply hj
  rw [←Walk.mem_verts_toSubgraph,hparts j,Walk.mem_verts_toSubgraph]
  exact hall j

/-- If every member contains every vertex of a whole cycle, the cycle
vertices occupy distinct endpoint slots outside the cycle member. -/
lemma common_cycle_length_bound (T : TrailFamily G k)
    (hk : Fintype.card V ≤ 2*k) (i : Fin k) {r : V}
    (C : G.Walk r r) (hc : C.IsCycle)
    (hi : (T.walk i).toSubgraph=C.toSubgraph)
    (hall : ∀ v ∈ C.support, ∀ j, v ∈ (T.walk j).support) :
    C.length+2 ≤ 2*k := by
  classical
  let W := {v : V // v ∈ C.support}
  let S := {j : Fin k // j ≠ i} × Bool
  have hex (v : W) : ∃ s : S, T.endpoint (s.1.val,s.2)=v.val := by
    obtain ⟨j,hji,hj⟩ := common_cycle_vertex_other_endpoint T hk i C hc hi v.property (hall v v.property)
    rcases hj with hj|hj
    · exact ⟨(⟨j,hji⟩,true),hj.symm⟩
    · exact ⟨(⟨j,hji⟩,false),hj.symm⟩
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro u v huv
    apply Subtype.ext
    rw [←hf u,←hf v,huv]
  have hb := Fintype.card_le_of_injective f hinj
  have hW : Fintype.card W=C.length := by
    simpa only [W,←Nat.card_eq_fintype_card,Set.ncard] using cycle_support_ncard hc
  have hS : Fintype.card S=(k-1)*2 := by
    simp only [S,Fintype.card_prod,Fintype.card_bool,Fintype.card_subtype_compl,
      Fintype.card_fin,Fintype.card_unique]
  have hkpos := i.isLt
  rw [hW,hS] at hb
  omega

/-- A nonempty path avoiding a cycle supplies two vertices outside it. -/
lemma cycle_avoiding_path_card {a b r : V} (C : G.Walk r r) (hc : C.IsCycle)
    (P : G.Walk a b) (hp : P.IsPath) (hn : ¬P.Nil)
    (havoid : ∀ x ∈ C.support, x ∉ P.support) :
    C.length+2 ≤ Fintype.card V := by
  classical
  have hd : Disjoint C.toSubgraph.verts P.toSubgraph.verts := by
    apply Set.disjoint_left.mpr
    intro x hxC hxP
    exact havoid x (by simpa using hxC) (by simpa using hxP)
  have hb := Set.ncard_le_card (C.toSubgraph.verts ∪ P.toSubgraph.verts)
  rw [Set.ncard_union_eq hd,Walk.verts_toSubgraph,cycle_support_ncard hc,
    (walk_vertex_ncard_eq_iff P).mpr hp,Nat.card_eq_fintype_card] at hb
  have hlen : 0 < P.length := Nat.pos_of_ne_zero (fun h ↦ hn (Walk.nil_iff_length_eq.mpr h))
  omega

/-- A whole five-cycle in a single-defect global maximum at the conjectured
vertex budget requires at least four members. -/
lemma five_cycle_four_slots (T : TrailFamily G k)
    (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (hk : Fintype.card V ≤ 2*k) (i : Fin k) {r : V}
    (C : G.Walk r r) (hc : C.IsCycle) (hl : C.length=5)
    (hi : (T.walk i).toSubgraph=C.toSubgraph) : 4 ≤ k := by
  classical
  have hnp := CycleEar.cycle_member_not_path T i C hc hi
  by_cases hall : ∀ v ∈ C.support, ∀ j, v ∈ (T.walk j).support
  · have hb := common_cycle_length_bound T hk i C hc hi hall
    omega
  · push_neg at hall
    obtain ⟨v,hv,j,hj⟩ := hall
    have hji : j ≠ i := by
      rintro rfl
      apply hj
      rwa [←Walk.mem_verts_toSubgraph,hi,Walk.mem_verts_toSubgraph]
    have hp := (T.one_defect_other_paths hs i hnp).2 j hji
    have hn := NilSlot.max_score_nonpath_no_nil T hm ⟨i,hnp⟩ j
    have havoid (x : V) (hx : x ∈ C.support) : x ∉ (T.walk j).support := by
      intro hxj
      exact hj ((PentagonIntersection.five_cycle_equal_members T hs hm i C hc hl hi hx hv j).mp hxj)
    have hb := cycle_avoiding_path_card C hc (T.walk j) hp hn havoid
    omega

end Erdos583CycleEndpointSlotsDevelopment
