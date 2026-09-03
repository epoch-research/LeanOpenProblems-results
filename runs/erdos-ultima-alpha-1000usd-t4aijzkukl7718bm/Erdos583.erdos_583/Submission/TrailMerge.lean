import Submission.Work

/-! Merge obstructions for unrestricted maximum-incidence trail families. -/
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery
open Erdos583Work.RootedTailSystem Erdos583Work.NilSlot Erdos583Work.TrailBudget
namespace Erdos583TrailMergeDevelopment
open scoped Classical
set_option maxHeartbeats 1200000

/-- Merge a two-member union into one trail and use the other slot for a nil
walk. If the old members meet at exactly one vertex, incidence score is unchanged. -/
lemma merge_into_nil {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (i j : Fin k) (hij : i ≠ j) {a : V}
    (r : G.Walk a (T.finish j)) (hr : r.IsTrail)
    (he : r.toSubgraph=(T.walk i).toSubgraph ⊔ (T.walk j).toSubgraph)
    (hi : ((T.walk i).toSubgraph.verts ∩ (T.walk j).toSubgraph.verts).ncard=1) :
    ∃ S : TrailFamily G k, S.score=T.score ∧ (S.walk i).Nil := by
  classical
  let p : G.Walk (T.finish i) (T.finish i) := Walk.nil
  have hp : p.IsTrail := Walk.IsTrail.nil
  have hd : Disjoint p.toSubgraph.edgeSet r.toSubgraph.edgeSet := by simp [p]
  have hu : p.toSubgraph.edgeSet ∪ r.toSubgraph.edgeSet =
      (T.walk i).toSubgraph.edgeSet ∪ (T.walk j).toSubgraph.edgeSet := by
    simp [p,he]
  obtain ⟨S,hSi,_,_,_,_,hs,_⟩ := replace_two_starts_general T i j hij (T.finish i) a p r hp hr hd hu
  have hn : (S.walk i).Nil := by
    apply Walk.nil_iff_length_eq.mpr
    rw [←trail_edgeSet_ncard _ (S.isTrail i),hSi]
    simp [p]
  have hcard := Set.ncard_union_add_ncard_inter (T.walk i).toSubgraph.verts (T.walk j).toSubgraph.verts
  rw [hi] at hcard
  have hrverts : r.toSubgraph.verts.ncard=
      ((T.walk i).toSubgraph.verts ∪ (T.walk j).toSubgraph.verts).ncard := by rw [he,Subgraph.verts_sup]
  rw [hrverts,show p.toSubgraph.verts.ncard=1 by simp [p]] at hs
  exact ⟨S,by omega,hn⟩

lemma paths_of_score_eq_maximal_nil {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T S : TrailFamily G k) (hmax : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (hs : S.score=T.score) (hn : ∃ i, (S.walk i).Nil) : ∀ i, (T.walk i).IsPath := by
  have hSmax : ∀ U : TrailFamily G k, U.score ≤ S.score := by
    intro U
    rw [hs]
    exact hmax U
  have hp := max_score_paths_of_nil S hSmax hn
  apply T.score_eq_edges_add_iff.mp
  rw [←hs]
  exact S.score_eq_edges_add_iff.mpr hp

lemma common_start_merge {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (i j : Fin k) (hij : i ≠ j)
    (hstart : T.start i=T.start j)
    (hi : ((T.walk i).toSubgraph.verts ∩ (T.walk j).toSubgraph.verts).ncard=1) :
    ∃ S : TrailFamily G k, S.score=T.score ∧ (S.walk i).Nil := by
  let q := (T.walk j).copy hstart.symm rfl
  let r := (T.walk i).reverse.append q
  have hq : q.IsTrail := by simpa [q] using T.isTrail j
  have hd : Disjoint (T.walk i).reverse.toSubgraph.edgeSet q.toSubgraph.edgeSet := by
    simpa [q] using T.disjoint hij
  have hr : r.IsTrail := trail_append_of_disjoint (T.isTrail i).reverse hq hd
  apply merge_into_nil T i j hij r hr _ hi
  simp only [r,q,Walk.toSubgraph_append,Walk.toSubgraph_reverse,NormalTrailSystem.walk_copy_subgraph]

/-- A repeated-vertex maximum has no two distinct members with a common start
and only one common vertex. -/
lemma common_start_intersection_bound {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (hmax : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (hnp : ∃ l, ¬(T.walk l).IsPath) (i j : Fin k) (hij : i ≠ j)
    (hstart : T.start i=T.start j) :
    2 ≤ ((T.walk i).toSubgraph.verts ∩ (T.walk j).toSubgraph.verts).ncard := by
  by_contra! hn
  have hpos : 0 < ((T.walk i).toSubgraph.verts ∩ (T.walk j).toSubgraph.verts).ncard := by
    apply (Set.ncard_pos (Set.toFinite _)).mpr
    exact ⟨T.start i,(T.walk i).start_mem_verts_toSubgraph,hstart.symm ▸ (T.walk j).start_mem_verts_toSubgraph⟩
  obtain ⟨S,hS,hSi⟩ := common_start_merge T i j hij hstart (by omega)
  obtain ⟨l,hl⟩ := hnp
  exact hl (paths_of_score_eq_maximal_nil T S hmax hS ⟨i,hSi⟩ l)

/-- The same obstruction applies to any shared endpoint, independently of the
chosen orientations of the two members. -/
lemma common_endpoint_intersection_bound {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (hmax : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (hnp : ∃ l, ¬(T.walk l).IsPath) (i j : Fin k) (hij : i ≠ j) (v : V)
    (hi : v=T.start i ∨ v=T.finish i) (hj : v=T.start j ∨ v=T.finish j) :
    2 ≤ ((T.walk i).toSubgraph.verts ∩ (T.walk j).toSubgraph.verts).ncard := by
  classical
  obtain ⟨S,hS,_,hparts⟩ := QuotaSurgery.orient T (fun l ↦ decide (T.finish l=v))
  have hstarts (l : Fin k) (hl : v=T.start l ∨ v=T.finish l) : S.start l=v := by
    rw [(hparts l).1]
    by_cases hb : T.finish l=v
    · simp [hb]
    · have ha : T.start l=v := hl.resolve_right (Ne.symm hb) |>.symm
      simp [hb,ha]
  have hSmax : ∀ U : TrailFamily G k, U.score ≤ S.score := by intro U; rw [hS]; exact hmax U
  have hSnp : ∃ l, ¬(S.walk l).IsPath := by
    by_contra! hp
    have hh := S.score_eq_edges_add_iff.mpr hp
    rw [hS] at hh
    obtain ⟨l,hl⟩ := hnp
    exact hl (T.score_eq_edges_add_iff.mp hh l)
  have hh := common_start_intersection_bound S hSmax hSnp i j hij
    ((hstarts i hi).trans (hstarts j hj).symm)
  simpa only [(hparts i).2.2,(hparts j).2.2] using hh

/-- A closed member intersecting another member at exactly one vertex can
likewise be merged at unchanged score, creating a nil slot. -/
lemma closed_merge {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (i j : Fin k) (hij : i ≠ j)
    (hclosed : T.start i=T.finish i)
    (hi : ((T.walk i).toSubgraph.verts ∩ (T.walk j).toSubgraph.verts).ncard=1) :
    ∃ S : TrailFamily G k, S.score=T.score ∧ (S.walk i).Nil := by
  classical
  obtain ⟨v,hv⟩ := (Set.ncard_pos (Set.toFinite _)).mp (show
      0 < ((T.walk i).toSubgraph.verts ∩ (T.walk j).toSubgraph.verts).ncard by omega)
  let c := (T.walk i).copy rfl hclosed.symm
  have hc : c.IsTrail := by simpa [c] using T.isTrail i
  have hvc : v ∈ c.support := by simpa [c] using (T.walk i).mem_verts_toSubgraph.mp hv.1
  let d := c.rotate hvc
  have hd : d.toSubgraph=(T.walk i).toSubgraph := by
    rw [Walk.toSubgraph_rotate]
    simp only [c,NormalTrailSystem.walk_copy_subgraph]
  obtain ⟨r,hr,he⟩ := splice_closed_at_vertex (T.walk j) d (T.isTrail j) (hc.rotate hvc)
    ((T.walk j).mem_verts_toSubgraph.mp hv.2) (by rw [hd]; exact T.disjoint hij.symm)
  apply merge_into_nil T i j hij r hr _ hi
  rw [he,hd,sup_comm]

lemma closed_intersection_bound {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (hmax : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (hnp : ∃ l, ¬(T.walk l).IsPath) (i j : Fin k) (hij : i ≠ j)
    (hclosed : T.start i=T.finish i)
    (hi : ((T.walk i).toSubgraph.verts ∩ (T.walk j).toSubgraph.verts).Nonempty) :
    2 ≤ ((T.walk i).toSubgraph.verts ∩ (T.walk j).toSubgraph.verts).ncard := by
  by_contra! hn
  have hpos := (Set.ncard_pos (Set.toFinite _)).mpr hi
  obtain ⟨S,hS,hSi⟩ := closed_merge T i j hij hclosed (by omega)
  obtain ⟨l,hl⟩ := hnp
  exact hl (paths_of_score_eq_maximal_nil T S hmax hS ⟨i,hSi⟩ l)

end Erdos583TrailMergeDevelopment
