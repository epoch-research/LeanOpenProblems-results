import Submission.Work

/-! Unconditional incidence improvement using a spare nil member. -/
open SimpleGraph Erdos583Work
open Erdos583Work.TrailNormalization Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery
open Erdos583Work.RootedTailSystem
namespace Erdos583NilSlotDevelopment
open scoped Classical
set_option maxHeartbeats 1200000

lemma nil_isPath {V : Type*} {G : SimpleGraph V} {a b : V}
    {p : G.Walk a b} (hp : p.Nil) : p.IsPath := by
  rw [Walk.isPath_def,Walk.nil_iff_support_eq.mp hp]
  simp

lemma nil_vertex_ncard {V : Type*} {G : SimpleGraph V} {a b : V}
    {p : G.Walk a b} (hp : p.Nil) : p.toSubgraph.verts.ncard=1 := by
  rw [Walk.verts_toSubgraph,Walk.nil_iff_support_eq.mp hp]
  simp

/-- A nil member can be relocated freely if endpoint quotas are not fixed. -/
lemma relocate_nil {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (j : Fin k) (hj : (T.walk j).Nil) (x : V) :
    ∃ S : TrailFamily G k, S.score=T.score ∧ S.start j=x ∧ S.finish j=x ∧
      (S.walk j).Nil ∧ ∀ i, i ≠ j →
        S.start i=T.start i ∧ S.finish i=T.finish i ∧ (S.walk i).toSubgraph=(T.walk i).toSubgraph := by
  classical
  let a (i : Fin k) := if i=j then x else T.start i
  let b (i : Fin k) := if i=j then x else T.finish i
  have hex (i : Fin k) : ∃ p : G.Walk (a i) (b i), p.IsTrail ∧
      p.toSubgraph.edgeSet=(T.walk i).toSubgraph.edgeSet ∧
      (i=j → p.Nil) ∧ (i ≠ j → p.toSubgraph=(T.walk i).toSubgraph) := by
    by_cases hi : i=j
    · subst i
      rw [show a j=x by simp [a],show b j=x by simp [b]]
      refine ⟨Walk.nil,Walk.IsTrail.nil,?_,fun _ ↦ Walk.Nil.nil,?_⟩
      · ext e
        simp only [Walk.mem_edges_toSubgraph,Walk.edges_nil,Walk.edges_eq_nil.mpr hj]
      · simp
    · rw [show a i=T.start i by simp [a,hi],show b i=T.finish i by simp [b,hi]]
      exact ⟨T.walk i,T.isTrail i,rfl,fun hh ↦ (hi hh).elim,fun _ ↦ rfl⟩
  choose p hp he hn he' using hex
  let S : TrailFamily G k :=
    { start := a,finish := b,walk := p,isTrail := hp
      disjoint := by intro i l hil; rw [he,he]; exact T.disjoint hil
      cover := by intro e; simp_rw [he]; exact T.cover e }
  refine ⟨S,?_,by simp [S,a],by simp [S,b],hn j rfl,?_⟩
  · apply Finset.sum_congr rfl
    intro i _
    change (p i).toSubgraph.verts.ncard=(T.walk i).toSubgraph.verts.ncard
    by_cases hi : i=j
    · subst i
      rw [nil_vertex_ncard (hn j rfl),nil_vertex_ncard hj]
    · rw [he' i hi]
  · intro i hi
    exact ⟨by simp [S,a,hi],by simp [S,b,hi],he' i hi⟩

/-- A nonpath walk has a cut whose two portions share two distinct vertices. -/
lemma nonpath_cut {V : Type*} [Fintype V] {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (hp : ¬p.IsPath) :
    ∃ x : V, ∃ L : G.Walk a x, ∃ R : G.Walk x b,
      p=L.append R ∧ 2 ≤ (L.toSubgraph.verts ∩ R.toSubgraph.verts).ncard := by
  classical
  obtain ⟨v,A,C,B,hCn,hform⟩ := walk_not_path_has_closed_segment p hp
  cases C with
  | nil => exact (hCn Walk.Nil.nil).elim
  | @cons v x v h Q =>
    let L := A.concat h
    let R := Q.append B
    have he : p=L.append R := by
      rw [hform]
      simp only [L,R,Walk.concat_append,Walk.cons_append]
    have hsub : ({v,x} : Set V) ⊆ L.toSubgraph.verts ∩ R.toSubgraph.verts := by
      intro z hz
      rcases (show z=v ∨ z=x by simpa using hz) with hz | hz
      · subst z
        constructor
        · change v ∈ (A.concat h).toSubgraph.verts
          rw [Walk.mem_verts_toSubgraph,Walk.support_concat]
          simpa only [List.concat_eq_append] using List.mem_append_left [x] A.end_mem_support
        · change v ∈ (Q.append B).toSubgraph.verts
          rw [Walk.mem_verts_toSubgraph,Walk.mem_support_append_iff]
          exact Or.inl Q.end_mem_support
      · subst z
        exact ⟨L.end_mem_verts_toSubgraph,R.start_mem_verts_toSubgraph⟩
    refine ⟨x,L,R,he,?_⟩
    have hh := Set.ncard_le_ncard hsub
    simpa only [Set.ncard_pair h.ne] using hh

/-- Splitting a repeated-vertex member into a nil slot strictly increases
incidence score. No endpoint quotas or connectivity assumptions are used. -/
lemma improve_using_nil {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (i j : Fin k) (hi : ¬(T.walk i).IsPath) (hj : (T.walk j).Nil) :
    ∃ U : TrailFamily G k, T.score < U.score := by
  classical
  have hij : i ≠ j := fun hh ↦ hi (hh ▸ nil_isPath hj)
  obtain ⟨x,L,R,hform,hint⟩ := nonpath_cut (T.walk i) hi
  have htrail : (L.append R).IsTrail := hform ▸ T.isTrail i
  obtain ⟨S,hS,_,hb,hn,hrest⟩ := relocate_nil T j hj x
  obtain ⟨_,hbi,hei⟩ := hrest i hij
  let p := R.copy rfl hbi.symm
  let q := L.copy rfl hb.symm
  have hp : p.IsTrail := by simpa [p] using htrail.of_append_right
  have hq : q.IsTrail := by simpa [q] using htrail.of_append_left
  have hd : Disjoint p.toSubgraph.edgeSet q.toSubgraph.edgeSet := by
    simpa [p,q] using (append_trail_disjoint htrail).symm
  have hu : p.toSubgraph.edgeSet ∪ q.toSubgraph.edgeSet =
      (S.walk i).toSubgraph.edgeSet ∪ (S.walk j).toSubgraph.edgeSet := by
    rw [hei,hform,Walk.toSubgraph_append,Subgraph.edgeSet_sup]
    have hejn : (S.walk j).toSubgraph.edgeSet=∅ := by
      ext e
      simp only [Walk.mem_edges_toSubgraph,Walk.edges_eq_nil.mpr hn,List.not_mem_nil,Set.mem_empty_iff_false]
    simp only [p,q,NormalTrailSystem.walk_copy_subgraph,hejn,Set.union_empty]
    exact Set.union_comm _ _
  obtain ⟨U,_,_,_,_,_,hscore,_⟩ := replace_two_starts_general S i j hij x (T.start i) p q hp hq hd hu
  have hcard := Set.ncard_union_add_ncard_inter L.toSubgraph.verts R.toSubgraph.verts
  have hverts : (T.walk i).toSubgraph.verts=L.toSubgraph.verts ∪ R.toSubgraph.verts := by
    rw [hform,Walk.toSubgraph_append,Subgraph.verts_sup]
  rw [←hverts] at hcard
  rw [nil_vertex_ncard hn,hei,hS] at hscore
  simp only [p,q,NormalTrailSystem.walk_copy_subgraph] at hscore
  exact ⟨U,by omega⟩

lemma max_score_paths_of_nil {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (hmax : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (hj : ∃ j, (T.walk j).Nil) : ∀ i, (T.walk i).IsPath := by
  obtain ⟨j,hj⟩ := hj
  intro i
  by_contra hi
  obtain ⟨U,hU⟩ := improve_using_nil T i j hi hj
  exact (not_lt_of_ge (hmax U)) hU

lemma max_score_nonpath_no_nil {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (hmax : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (hi : ∃ i, ¬(T.walk i).IsPath) : ∀ j, ¬(T.walk j).Nil := by
  intro j hj
  obtain ⟨i,hi⟩ := hi
  exact hi (max_score_paths_of_nil T hmax ⟨j,hj⟩ i)

end Erdos583NilSlotDevelopment
