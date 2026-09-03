import Submission.RootEndpointTailCapacity

/-! Charging root endpoint slots to distinct vertices on the retained tail. -/
namespace Erdos583RootQuotaTailBoundDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery Erdos583Work.LollipopEar
open Erdos583LollipopEndpointRotationDevelopment
open scoped Classical
set_option maxHeartbeats 2400000
set_option Elab.async false

lemma root_slot_index_injective {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (r : V) (hne : ∀ j, T.start j ≠ T.finish j) :
    Function.Injective (fun s : {s : Fin k × Bool // T.endpoint s=r} ↦ s.val.1) := by
  intro s t hst
  change s.val.1=t.val.1 at hst
  apply Subtype.ext
  apply Prod.ext hst
  have hs := s.property
  have ht := t.property
  dsimp only [TrailFamily.endpoint] at hs ht
  rw [←hst] at ht
  cases ha : s.val.2 <;> cases hb : t.val.2
  · rfl
  · simp only [ha,hb,Bool.false_eq_true,if_false,if_true] at hs ht
    exact (hne s.val.1 (ht.trans hs.symm)).elim
  · simp only [ha,hb,Bool.false_eq_true,if_false,if_true] at hs ht
    exact (hne s.val.1 (hs.trans ht.symm)).elim
  · rfl

lemma simple_member_from_root_slot {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (r : V) (s : Fin k × Bool) (hs : T.endpoint s=r)
    (hp : (T.walk s.1).IsPath) :
    ∃ b, ∃ P : G.Walk r b, P.IsPath ∧ (T.walk s.1).toSubgraph=P.toSubgraph := by
  rcases s with ⟨j,c⟩
  cases c
  · have he : T.finish j=r := hs
    exact ⟨T.start j,(T.walk j).reverse.copy he rfl,
      by simpa using hp.reverse,
      by simp only [NormalTrailSystem.walk_copy_subgraph,Walk.toSubgraph_reverse]⟩
  · have he : T.start j=r := hs
    exact ⟨T.finish j,(T.walk j).copy he rfl,
      by simpa using hp,
      by simp only [NormalTrailSystem.walk_copy_subgraph]⟩

lemma minimum_root_quota_le_tail_length_add_one {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k : ℕ} (T : TrailFamily G k)
    (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (r : V) (L : RootedCycleRep T r) (hn : ¬L.tail.Nil)
    (hmin : ∀ W : TrailFamily G k, ∀ s : V, ∀ M : RootedCycleRep W s,
      W.score=T.score → L.cycle.length ≤ M.cycle.length) :
    T.quota r ≤ L.tail.length+1 := by
  classical
  have hnp := L.member_not_path
  have hother := (T.one_defect_other_paths hs L.index hnp).2
  have hnil := NilSlot.max_score_nonpath_no_nil T hm ⟨L.index,hnp⟩
  have hne (j : Fin k) : T.start j ≠ T.finish j := by
    by_cases hji : j=L.index
    · subst j
      rw [L.start_eq,L.finish_eq]
      exact ContiguousRegion.path_ends_ne L.tail L.isPath hn
    · exact ContiguousRegion.path_ends_ne (T.walk j) (hother j hji) (hnil j)
  let E := {s : Fin k × Bool // T.endpoint s=r}
  have hdata (s : E) : ∃ w ∈ L.tail.toSubgraph.verts,
      (s.val.1=L.index → w=r) ∧
      (s.val.1 ≠ L.index → w ≠ r ∧ s(w,L.cycle.snd) ∈ (T.walk s.val.1).toSubgraph.edgeSet) := by
    by_cases hi : s.val.1=L.index
    · exact ⟨r,L.tail.start_mem_verts_toSubgraph,fun _ ↦ rfl,fun h ↦ (h hi).elim⟩
    · obtain ⟨b,P,hP,hPe⟩ := simple_member_from_root_slot T r s.val s.property (hother s.val.1 hi)
      obtain ⟨w,A,f,B,hform,hwS,hwC⟩ := minimum_lollipop_root_path_predecessor T hm r L hmin
        s.val.1 (Ne.symm hi) (L.cycle.toSubgraph_adj_snd L.isCycle.not_nil) P hP hPe
      refine ⟨w,L.tail.mem_verts_toSubgraph.mpr hwS,fun he ↦ (hi he).elim,fun _ ↦ ⟨?_,?_⟩⟩
      · exact fun he ↦ hwC (he ▸ L.cycle.start_mem_support)
      · rw [hPe,hform]
        simp
  choose w hw hwi hwo using hdata
  let f : E → L.tail.toSubgraph.verts := fun s ↦ ⟨w s,hw s⟩
  have hf : Function.Injective f := by
    intro s t he
    have hew : w s=w t := congrArg Subtype.val he
    apply root_slot_index_injective T r hne
    by_cases hsi : s.val.1=L.index
    · have hsr := hwi s hsi
      have hti : t.val.1=L.index := by
        by_contra hti
        exact (hwo t hti).1 (hew.symm.trans hsr)
      exact hsi.trans hti.symm
    · by_cases hti : t.val.1=L.index
      · exact ((hwo s hsi).1 (hew.trans (hwi t hti))).elim
      · by_contra hst
        exact Set.disjoint_left.mp (T.disjoint hst) (hwo s hsi).2 (hew.symm ▸ (hwo t hti).2)
  change Nat.card E ≤ _
  calc
    Nat.card E ≤ Nat.card L.tail.toSubgraph.verts := Nat.card_le_card_of_injective f hf
    _=L.tail.length+1 := InducedBuffer.path_vertex_ncard L.tail L.isPath

end Erdos583RootQuotaTailBoundDevelopment
