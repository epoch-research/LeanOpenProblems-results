import Submission.EndpointRotation

/-! The branch bijection at a vertex of an endpoint path packing.  It records
actual path branches, rather than just the earlier cardinality comparison. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.OddPaths
set_option maxHeartbeats 600000
variable {V : Type*} {G : SimpleGraph V}

lemma edge_owner_unique {L : List (Piece G)} (hn : (edgeList L).Nodup)
    {p q : Piece G} (hp : p ∈ L) (hq : q ∈ L) {e : Sym2 V}
    (hep : e ∈ p.walk.edges) (heq : e ∈ q.walk.edges) : p = q := by
  by_contra hne
  obtain ⟨M,hM⟩ := two_at_front hp hq (Ne.symm hne)
  have hh := (edgeList_perm hM).nodup_iff.mp hn
  change (p.walk.edges ++ (q.walk.edges ++ edgeList M)).Nodup at hh
  exact hh.disjoint hep (List.mem_append_left _ heq)

lemma dart_ne_symm_in_trail {a b : V} (p : G.Walk a b) (hp : p.IsTrail)
    {d : G.Dart} (hd : d ∈ p.darts) : d.symm ∉ p.darts := by
  intro hs
  have hi := (List.nodup_map_iff_inj_on hp.edges_nodup.of_map).mp hp.edges_nodup
  have he : d = d.symm := hi d hd d.symm hs (by simp)
  exact d.fst_ne_snd (congrArg (fun e : G.Dart => e.fst) he)

/-- At vertex `v`, the neighbor `w` lies on the branch towards endpoint `a`
of its packed path.  Darts distinguish the two branches of a path through `v`. -/
def Branch (L : List (Piece G)) (v a w : V) : Prop :=
  ∃ p ∈ L, ∃ hvw : G.Adj v w,
    (a = p.src ∧ (⟨(w,v),hvw.symm⟩ : G.Dart) ∈ p.walk.darts) ∨
    (a = p.dst ∧ (⟨(v,w),hvw⟩ : G.Dart) ∈ p.walk.darts)

lemma Branch.covered {L : List (Piece G)} {v a w : V} (h : Branch L v a w) :
    (coveredGraph L).Adj v w := by
  obtain ⟨p,hp,hvw,h⟩ := h
  apply (coveredGraph_adj L v w).mpr
  refine List.mem_flatMap.mpr ⟨p,hp,?_⟩
  rcases h with ⟨_,hd⟩ | ⟨_,hd⟩
  · have he := List.mem_map_of_mem (f := Dart.edge) hd
    simpa only [Walk.edges,Dart.edge_mk,Sym2.eq_swap] using he
  · exact List.mem_map_of_mem (f := Dart.edge) hd

lemma Branch.endpoint_unique {L : List (Piece G)} (hn : (edgeList L).Nodup)
    {v a b w : V} (ha : Branch L v a w) (hb : Branch L v b w) : a = b := by
  obtain ⟨p,hp,hvw,ha⟩ := ha
  obtain ⟨q,hq,_,hb⟩ := hb
  have hmem (r : Piece G)
      (h : (⟨(w,v),hvw.symm⟩ : G.Dart) ∈ r.walk.darts ∨
        (⟨(v,w),hvw⟩ : G.Dart) ∈ r.walk.darts) : s(v,w) ∈ r.walk.edges := by
    rcases h with h | h
    · have he := List.mem_map_of_mem (f := Dart.edge) h
      simpa only [Walk.edges,Dart.edge_mk,Sym2.eq_swap] using he
    · exact List.mem_map_of_mem (f := Dart.edge) h
  have hpq := edge_owner_unique hn hp hq (hmem p (ha.imp And.right And.right))
    (hmem q (hb.imp And.right And.right))
  subst q
  rcases ha with ⟨ha,ha'⟩ | ⟨ha,ha'⟩ <;>
    rcases hb with ⟨hb,hb'⟩ | ⟨hb,hb'⟩
  · exact ha.trans hb.symm
  · exact (dart_ne_symm_in_trail p.walk p.isPath.isTrail ha' hb').elim
  · exact (dart_ne_symm_in_trail p.walk p.isPath.isTrail ha' hb').elim
  · exact ha.trans hb.symm

lemma exists_branch [Fintype V] {L : List (Piece G)} {v a : V}
    (ha : a ∈ (touchingEndpoints L v).erase v) : ∃ w, Branch L v a w := by
  have hav : a ≠ v := (Finset.mem_erase.mp ha).1
  have he : a ∈ endpoints (touchingPaths L v) :=
    List.mem_toFinset.mp (Finset.mem_erase.mp ha).2
  obtain ⟨p,hp,hep⟩ := List.mem_flatMap.mp he
  obtain ⟨hp,hv⟩ := mem_touchingPaths.mp hp
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hep
  rcases hep with hep | hep
  · subst a
    obtain ⟨w,A,B,hwv,heq⟩ := Rotation.split_before p.walk hv hav
    refine ⟨w,p,hp,hwv.symm,Or.inl ⟨rfl,?_⟩⟩
    rw [heq]
    simp [Walk.darts_append]
  · subst a
    have hvr : v ∈ p.walk.reverse.support := by simpa using hv
    obtain ⟨w,A,B,hwv,heq⟩ := Rotation.split_before p.walk.reverse hvr hav
    refine ⟨w,p,hp,hwv.symm,Or.inr ⟨rfl,?_⟩⟩
    have hd : (⟨(w,v),hwv⟩ : G.Dart) ∈ p.walk.reverse.darts := by
      rw [heq]
      simp [Walk.darts_append]
    exact Walk.mem_darts_reverse.mp hd

noncomputable def branchMap [Fintype V] (L : List (Piece G)) (v : V) :
    {a // a ∈ (touchingEndpoints L v).erase v} →
      {w // w ∈ (coveredGraph L).neighborFinset v} := fun a =>
  ⟨(exists_branch a.property).choose,
    ((coveredGraph L).mem_neighborFinset _ _).mpr (exists_branch a.property).choose_spec.covered⟩

lemma branchMap_spec [Fintype V] (L : List (Piece G)) (v : V)
    (a : {a // a ∈ (touchingEndpoints L v).erase v}) :
    Branch L v a.val (branchMap L v a).val := (exists_branch a.property).choose_spec

lemma branchMap_injective [Fintype V] {L : List (Piece G)} (hn : (edgeList L).Nodup) (v : V) :
    Function.Injective (branchMap L v) := by
  intro a b hab
  apply Subtype.ext
  have he := congrArg Subtype.val hab
  exact (branchMap_spec L v a).endpoint_unique hn (he ▸ branchMap_spec L v b)

lemma Admissible.branchMap_bijective [Fintype V] {L : List (Piece G)}
    (hL : Admissible L) (v : V) : Function.Bijective (branchMap L v) := by
  have hc : Fintype.card {a // a ∈ (touchingEndpoints L v).erase v} =
      Fintype.card {w // w ∈ (coveredGraph L).neighborFinset v} := by
    simp only [Fintype.card_coe]
    have he := hL.touchingEndpoints_card v
    have hv := hL.mem_touchingEndpoints_self v
    have hr := Finset.card_erase_add_one hv
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    omega
  exact (Fintype.bijective_iff_injective_and_card (branchMap L v)).mpr ⟨branchMap_injective hL.1 v,hc⟩

end Erdos184Work.OddPaths
#print axioms Erdos184Work.OddPaths.Admissible.branchMap_bijective
