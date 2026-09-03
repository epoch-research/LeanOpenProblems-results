import Submission.Work

/-! Closed-segment relocation and its exact incidence cost. -/

open SimpleGraph Erdos583Work Erdos583Work.RootedTailSystem
open Erdos583Work.TrailNormalization Erdos583Work.PendantCompletion
open Erdos583Work.LeafPermutation Erdos583Work.DefectTransport
namespace Erdos583CycleRelocationDevelopment
open scoped Classical
set_option maxHeartbeats 1200000

/-- Moving a closed segment between two edge-disjoint trails preserves the edge
partition. It need not preserve the vertex-incidence score. -/
lemma relocate_cycle_data {V : Type*} {G : SimpleGraph V} {a c d : V}
    (r : G.Walk a c) (C : G.Walk c c) (q : G.Walk c d)
    (hrC : (r.append C).IsTrail) (hq : q.IsTrail)
    (hd : Disjoint (r.append C).toSubgraph.edgeSet q.toSubgraph.edgeSet) :
    r.IsTrail ∧ (C.append q).IsTrail ∧
      Disjoint r.toSubgraph.edgeSet (C.append q).toSubgraph.edgeSet ∧
      r.toSubgraph.edgeSet ∪ (C.append q).toSubgraph.edgeSet =
        (r.append C).toSubgraph.edgeSet ∪ q.toSubgraph.edgeSet := by
  rw [Walk.toSubgraph_append,Subgraph.edgeSet_sup] at hd
  obtain ⟨hrq,hCq⟩ := disjoint_sup_left.mp hd
  refine ⟨hrC.of_append_left,trail_append_of_disjoint hrC.of_append_right hq hCq,?_,?_⟩
  · rw [Walk.toSubgraph_append,Subgraph.edgeSet_sup]
    exact disjoint_sup_right.mpr ⟨append_trail_disjoint hrC,hrq⟩
  · simp only [Walk.toSubgraph_append,Subgraph.edgeSet_sup,Set.union_assoc]

/-- The incidence change is exactly the difference between the two overlaps
with the transferred closed segment. No disjoint-support assumption is hidden. -/
lemma relocate_cycle_ncard {V : Type*} [Fintype V] {G : SimpleGraph V}
    {a c d : V} (r : G.Walk a c) (C : G.Walk c c) (q : G.Walk c d) :
    r.toSubgraph.verts.ncard + (C.append q).toSubgraph.verts.ncard +
        (C.toSubgraph.verts ∩ q.toSubgraph.verts).ncard =
      (r.append C).toSubgraph.verts.ncard + q.toSubgraph.verts.ncard +
        (r.toSubgraph.verts ∩ C.toSubgraph.verts).ncard := by
  simp only [Walk.toSubgraph_append,Subgraph.verts_sup]
  have h₁ := Set.ncard_union_add_ncard_inter r.toSubgraph.verts C.toSubgraph.verts
  have h₂ := Set.ncard_union_add_ncard_inter C.toSubgraph.verts q.toSubgraph.verts
  omega

lemma path_split_verts_inter {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {a b c : V} (p : G.Walk a b) (hp : p.IsPath) (hc : c ∈ p.support) :
    (p.takeUntil c hc).toSubgraph.verts ∩ (p.dropUntil c hc).toSubgraph.verts = {c} := by
  ext x
  constructor
  · rintro ⟨hx,hy⟩
    have hpath : ((p.takeUntil c hc).append (p.dropUntil c hc)).IsPath := by simpa using hp
    by_contra hx'
    have hxc : x ≠ c := by simpa using hx'
    exact (hpath.ne_of_mem_support_of_append hxc
      ((p.takeUntil c hc).mem_verts_toSubgraph.mp hx)
      ((p.dropUntil c hc).mem_verts_toSubgraph.mp hy)) rfl
  · intro hx
    have he : x = c := Set.mem_singleton_iff.mp hx
    subst x
    exact ⟨(p.takeUntil c hc).mem_verts_toSubgraph.mpr (p.takeUntil c hc).end_mem_support,
      (p.dropUntil c hc).mem_verts_toSubgraph.mpr (p.dropUntil c hc).start_mem_support⟩

/-- A terminal cycle extracted from a path plus one edge meets the preceding
simple prefix only at its base vertex. -/
lemma terminal_cycle_prefix_inter {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {a b c : V} (p : G.Walk a b) (hp : p.IsPath) (h : G.Adj b c)
    (hc : c ∈ p.support) :
    (p.takeUntil c hc).toSubgraph.verts ∩
      ((p.dropUntil c hc).concat h).toSubgraph.verts = {c} := by
  have he : ((p.dropUntil c hc).concat h).toSubgraph.verts =
      (p.dropUntil c hc).toSubgraph.verts := by
    ext x
    simp only [Walk.mem_verts_toSubgraph,Walk.support_concat,List.concat_eq_append,List.mem_append,
      List.mem_singleton]
    constructor
    · rintro (hx | hx)
      · exact hx
      · exact hx.symm ▸ (p.dropUntil c hc).start_mem_support
    · exact Or.inl
  rw [he]
  exact path_split_verts_inter p hp hc

/-- For a terminal cycle, a relocation loses one incidence for every extra
intersection of the receiving trail with that cycle. The base intersection
itself is already present on both sides. -/
lemma terminal_cycle_relocation_ncard {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {a b c d : V} (p : G.Walk a b) (hp : p.IsPath)
    (h : G.Adj b c) (hc : c ∈ p.support) (q : G.Walk c d) :
    let r := p.takeUntil c hc
    let C := (p.dropUntil c hc).concat h
    (leafWalk r).toSubgraph.verts.ncard + (leafWalk (C.append q)).toSubgraph.verts.ncard +
        (C.toSubgraph.verts ∩ q.toSubgraph.verts).ncard =
      (leafWalk (p.concat h)).toSubgraph.verts.ncard + (leafWalk q).toSubgraph.verts.ncard + 1 := by
  dsimp only
  simp only [leafWalk_ncard]
  have hh := relocate_cycle_ncard (p.takeUntil c hc) ((p.dropUntil c hc).concat h) q
  rw [terminal_cycle_prefix_inter p hp h hc,Set.ncard_singleton,
    Walk.append_concat,Walk.take_spec] at hh
  omega

/-- An additional cycle/receiver intersection forces a strict score loss in
this specific relocation. Thus the move cannot be silently treated as a
score-preserving exposure of the internal defect. -/
lemma terminal_cycle_relocation_strict_loss {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {a b c d x : V} (p : G.Walk a b) (hp : p.IsPath)
    (h : G.Adj b c) (hc : c ∈ p.support) (q : G.Walk c d)
    (hxc : x ≠ c) (hxC : x ∈ ((p.dropUntil c hc).concat h).support)
    (hxq : x ∈ q.support) :
    (leafWalk (p.takeUntil c hc)).toSubgraph.verts.ncard +
        (leafWalk (((p.dropUntil c hc).concat h).append q)).toSubgraph.verts.ncard + 1 ≤
      (leafWalk (p.concat h)).toSubgraph.verts.ncard + (leafWalk q).toSubgraph.verts.ncard := by
  let C := (p.dropUntil c hc).concat h
  have hsub : {c,x} ⊆ C.toSubgraph.verts ∩ q.toSubgraph.verts := by
    intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | hz
    · exact ⟨C.mem_verts_toSubgraph.mpr C.start_mem_support,
        q.mem_verts_toSubgraph.mpr q.start_mem_support⟩
    · rw [Set.mem_singleton_iff.mp hz]
      exact ⟨C.mem_verts_toSubgraph.mpr hxC,q.mem_verts_toSubgraph.mpr hxq⟩
  have htwo : 2 ≤ (C.toSubgraph.verts ∩ q.toSubgraph.verts).ncard := by
    simpa only [Set.ncard_pair hxc.symm] using Set.ncard_le_ncard hsub
  have hh := terminal_cycle_relocation_ncard p hp h hc q
  dsimp only at hh
  change 2 ≤ (((p.dropUntil c hc).concat h).toSubgraph.verts ∩ q.toSubgraph.verts).ncard at htwo
  omega

end Erdos583CycleRelocationDevelopment
