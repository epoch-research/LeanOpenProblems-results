import Submission.Work

/-! Exact transport of a pendant purification defect along a short core edge. -/

open SimpleGraph Erdos583Work Erdos583Work.RootedTailSystem
open Erdos583Work.TrailNormalization Erdos583Work.PendantCompletion
open Erdos583Work.LeafPermutation
namespace Erdos583DefectTransportDevelopment
open scoped Classical

set_option maxHeartbeats 1200000

/-- A finish-label version of the tracked two-member replacement. -/
lemma replace_two_finishes_tracked {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem G k) (i j : Fin k) (hij : i ≠ j)
    (p : G.Walk (T.start i) (T.finish j)) (q : G.Walk (T.start j) (T.finish i))
    (hp : p.IsTrail) (hq : q.IsTrail)
    (hpq : Disjoint p.toSubgraph.edgeSet q.toSubgraph.edgeSet)
    (hu : p.toSubgraph.edgeSet ∪ q.toSubgraph.edgeSet =
      (T.walk i).toSubgraph.edgeSet ∪ (T.walk j).toSubgraph.edgeSet) :
    ∃ S : NormalTrailSystem G k,
      (S.walk i).toSubgraph = p.toSubgraph ∧
      (S.walk j).toSubgraph = q.toSubgraph ∧
      (∀ l, l ≠ i → l ≠ j → (S.walk l).toSubgraph = (T.walk l).toSubgraph) ∧
      S.start = T.start ∧ S.finish = (fun l ↦ T.finish (Equiv.swap i j l)) ∧
      S.score + (T.walk i).toSubgraph.verts.ncard + (T.walk j).toSubgraph.verts.ncard =
        T.score + p.toSubgraph.verts.ncard + q.toSubgraph.verts.ncard := by
  classical
  obtain ⟨U,hU,hUi⟩ := T.orient (fun _ ↦ true)
  have ha (l) : U.start l = T.finish l := by simpa using (hUi l).1
  have hb (l) : U.finish l = T.start l := by simpa using (hUi l).2.1
  let p' := p.reverse.copy (ha j).symm (hb i).symm
  let q' := q.reverse.copy (ha i).symm (hb j).symm
  have hp' : p'.IsTrail := by simpa [p'] using hp.reverse
  have hq' : q'.IsTrail := by simpa [q'] using hq.reverse
  have heP : p'.toSubgraph = p.toSubgraph := by rw [NormalTrailSystem.walk_copy_subgraph,Walk.toSubgraph_reverse]
  have heQ : q'.toSubgraph = q.toSubgraph := by rw [NormalTrailSystem.walk_copy_subgraph,Walk.toSubgraph_reverse]
  obtain ⟨R,hRi,hRj,hRl,hRa,hRb,hs⟩ := replace_two_starts_tracked U i j hij p' q' hp' hq'
    (by rw [heP,heQ]; exact hpq)
    (by rw [heP,heQ,(hUi i).2.2,(hUi j).2.2]; exact hu)
  obtain ⟨S,hS,hSl⟩ := R.orient (fun _ ↦ true)
  refine ⟨S,((hSl i).2.2.trans hRi).trans heP,((hSl j).2.2.trans hRj).trans heQ,?_,?_,?_,?_⟩
  · intro l hli hlj
    exact (hSl l).2.2.trans ((hRl l hli hlj).trans (hUi l).2.2)
  · funext l
    have hh : S.start l = R.finish l := by simpa using (hSl l).1
    rw [hh,hRb,hb]
  · funext l
    have hh : S.finish l = R.start l := by simpa using (hSl l).2.1
    rw [hh,hRa]
    exact ha _
  · rw [(hUi i).2.2,(hUi j).2.2,hU,heP,heQ] at hs
    rwa [hS]

lemma leafWalk_isTrail {V : Type*} {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (hp : p.IsTrail) : (leafWalk p).IsTrail := by
  have hmap : (p.map (inclusion G Set.univ)).IsTrail :=
    Walk.map_isTrail_of_injective (f := inclusion G Set.univ) Sum.inl_injective hp
  have hr : ((leafWalk p).reverse).IsTrail := by
    rw [leafWalk,Walk.reverse_concat]
    apply (Walk.isTrail_cons _ _).mpr
    refine ⟨hmap.reverse,?_⟩
    simp only [Walk.edges_reverse,List.mem_reverse,Walk.edges_map,List.mem_map,not_exists,not_and]
    intro x _ hx
    change Sym2.map (Sum.inl : V → V ⊕ (Set.univ : Set V)) x = s(Sum.inr ⟨b,Set.mem_univ _⟩,Sum.inl b) at hx
    exact inl_edge_ne_cross x b ⟨b,Set.mem_univ _⟩ (hx.trans Sym2.eq_swap)
  simpa using hr.reverse

lemma leafWalk_ncard {V : Type*} [Fintype V] {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) : (leafWalk p).toSubgraph.verts.ncard = p.toSubgraph.verts.ncard + 1 := by
  have he : (leafWalk p).toSubgraph.verts =
      insert (Sum.inr ⟨b,Set.mem_univ b⟩) (Sum.inl '' p.toSubgraph.verts) := by
    ext z
    simp [leafWalk,Walk.support_map,inclusion,Walk.verts_toSubgraph,or_comm]
  rw [he,Set.ncard_insert_of_notMem (by simp),Set.ncard_image_of_injective _ Sum.inl_injective]

lemma concat_ncard {V : Type*} [Fintype V] {G : SimpleGraph V} {a b c : V}
    (p : G.Walk a b) (h : G.Adj b c) :
    (p.concat h).toSubgraph.verts.ncard + (if c ∈ p.support then 1 else 0) =
      p.toSubgraph.verts.ncard + 1 := by
  classical
  have he : (p.concat h).toSubgraph = (Walk.cons h.symm p.reverse).toSubgraph := by
    rw [← Walk.reverse_concat,Walk.toSubgraph_reverse]
  rw [he]
  by_cases hc : c ∈ p.support
  · rw [cons_ncard_of_mem _ _ (by simpa using hc),Walk.toSubgraph_reverse,if_pos hc]
  · rw [cons_ncard_of_notMem _ _ (by simpa using hc),Walk.toSubgraph_reverse,if_neg hc]

/-- Appending a new core edge to a lifted path stays simple exactly when its
new endpoint has not previously occurred. -/
lemma leafWalk_concat_isPath_iff {V : Type*} {G : SimpleGraph V} {a b c : V}
    (p : G.Walk a b) (hp : p.IsPath) (h : G.Adj b c) :
    (leafWalk (p.concat h)).IsPath ↔ c ∉ p.support := by
  constructor
  · intro hq
    have hr := (project_path_support _ hq).1
    rw [leafWalk_project] at hr
    exact (Walk.concat_isPath_iff h).mp hr |>.2
  · intro hc
    exact leafWalk_isPath _ (hp.concat hc h)

/-- When the new endpoint already occurs on the path and the appended edge is
unused, the resulting trail consists of a simple prefix followed by a simple
cycle. In the pendant lift this is an internal, not an endpoint, repetition. -/
lemma concat_terminal_cycle {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {a b c : V} (p : G.Walk a b) (hp : p.IsPath) (h : G.Adj b c)
    (hc : c ∈ p.support) (hn : s(b,c) ∉ p.edges) :
    (p.takeUntil c hc).IsPath ∧ ((p.dropUntil c hc).concat h).IsCycle ∧
      p.concat h = (p.takeUntil c hc).append ((p.dropUntil c hc).concat h) := by
  refine ⟨hp.takeUntil hc,?_,?_⟩
  · rw [← Walk.isCycle_reverse,Walk.reverse_concat]
    apply (Walk.cons_isCycle_iff _ _).mpr
    refine ⟨(hp.dropUntil hc).reverse,?_⟩
    intro he
    apply hn
    have he' : s(b,c) ∈ (p.dropUntil c hc).edges := by
      simpa only [Walk.edges_reverse,List.mem_reverse,Sym2.eq_swap] using he
    have hh : s(b,c) ∈ ((p.takeUntil c hc).append (p.dropUntil c hc)).edges := by
      simp only [Walk.edges_append,List.mem_append]
      exact Or.inr he'
    simpa using hh
  · rw [Walk.append_concat,Walk.take_spec]

/-- Moving a short core edge to the preceding leaf-ended trail purifies its
old endpoint. The only incidence loss is whether the new endpoint was already
on that preceding trail. -/
lemma pendant_transfer_data {V : Type*} [Fintype V] {G : SimpleGraph V} {a b c : V}
    (p : G.Walk a b) (hp : p.IsTrail) (h : G.Adj b c) (hn : s(b,c) ∉ p.edges) :
    let P := leafWalk (p.concat h)
    let Q := leafWalk (Walk.nil : G.Walk b b)
    P.IsTrail ∧ Q.IsTrail ∧ Disjoint P.toSubgraph.edgeSet Q.toSubgraph.edgeSet ∧
      P.toSubgraph.edgeSet ∪ Q.toSubgraph.edgeSet =
        (leafWalk p).toSubgraph.edgeSet ∪ (leafWalk (Walk.cons h Walk.nil)).toSubgraph.edgeSet ∧
      P.toSubgraph.verts.ncard + Q.toSubgraph.verts.ncard + (if c ∈ p.support then 1 else 0) =
        (leafWalk p).toSubgraph.verts.ncard + (leafWalk (Walk.cons h Walk.nil)).toSubgraph.verts.ncard := by
  classical
  have hpc : (p.concat h).IsTrail := by
    have hr : ((p.concat h).reverse).IsTrail := by
      rw [Walk.reverse_concat]
      apply (Walk.isTrail_cons _ _).mpr
      exact ⟨hp.reverse,by simpa only [Walk.edges_reverse,List.mem_reverse,Sym2.eq_swap] using hn⟩
    simpa using hr.reverse
  refine ⟨leafWalk_isTrail _ hpc,(leafWalk_isPath _ Walk.IsPath.nil).isTrail,?_,?_,?_⟩
  · apply Set.disjoint_left.mpr
    intro d hd hd'
    have he : d = s(Sum.inl b,Sum.inr ⟨b,Set.mem_univ _⟩) := by
      rw [leafWalk_edges] at hd'
      simpa using hd'
    rw [leafWalk_edges] at hd
    rcases hd with ⟨x,_,hx⟩ | hc
    · exact inl_edge_ne_cross x b ⟨b,Set.mem_univ _⟩ (hx.trans he)
    · have hh := he.symm.trans hc
      rcases Sym2.eq_iff.mp hh with hh | hh
      · exact h.ne (Sum.inl.inj hh.1)
      · exact Sum.inl_ne_inr hh.1
  · ext d
    simp only [Set.mem_union,leafWalk_edges]
    simp only [Walk.mem_edges_toSubgraph,Walk.edges_concat,
      Walk.edges_cons,Walk.edges_nil,List.concat_eq_append,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
    constructor
    · rintro ((⟨x,hx,hxd⟩ | hd) | (⟨x,hx,_⟩ | hd))
      · rcases hx with hx | rfl
        · exact Or.inl (Or.inl ⟨x,hx,hxd⟩)
        · exact Or.inr (Or.inl ⟨s(b,c),rfl,hxd⟩)
      · exact Or.inr (Or.inr hd)
      · exact hx.elim
      · exact Or.inl (Or.inr hd)
    · rintro ((⟨x,hx,hxd⟩ | hd) | (⟨x,hx,hxd⟩ | hd))
      · exact Or.inl (Or.inl ⟨x,Or.inl hx,hxd⟩)
      · exact Or.inr (Or.inr hd)
      · exact Or.inl (Or.inl ⟨x,Or.inr hx,hxd⟩)
      · exact Or.inl (Or.inr hd)
  · simp only [leafWalk_ncard]
    have hh := concat_ncard p h
    have hnil : (Walk.nil : G.Walk b b).toSubgraph.verts.ncard = 1 := by simp
    have hedge : (Walk.cons h Walk.nil).toSubgraph.verts.ncard = 2 := by
      simp [Walk.toSubgraph,subgraphOfAdj_verts,h.ne]
    rw [hnil,hedge]
    omega

/-- Perform the pendant transfer inside a full normal trail system. The old
core endpoint b becomes paired with its own leaf, every other member is retained,
and the exact possible one-incidence loss is recorded. -/
lemma transfer_pendant_defect {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem (allLeafCompletion G) k) (i j : Fin k) (hij : i ≠ j)
    {a b c : V} (p : G.Walk a b) (hp : p.IsTrail) (h : G.Adj b c)
    (hai : T.start i = Sum.inl a) (hbi : T.finish i = Sum.inr ⟨b,Set.mem_univ _⟩)
    (haj : T.start j = Sum.inl b) (hbj : T.finish j = Sum.inr ⟨c,Set.mem_univ _⟩)
    (hi : (T.walk i).toSubgraph = (leafWalk p).toSubgraph)
    (hj : (T.walk j).toSubgraph = (leafWalk (Walk.cons h Walk.nil)).toSubgraph) :
    ∃ S : NormalTrailSystem (allLeafCompletion G) k,
      S.score + (if c ∈ p.support then 1 else 0) = T.score ∧
      (S.walk i).toSubgraph = (leafWalk (p.concat h)).toSubgraph ∧
      (S.walk j).toSubgraph = (leafWalk (Walk.nil : G.Walk b b)).toSubgraph ∧
      (∀ l, l ≠ i → l ≠ j → (S.walk l).toSubgraph = (T.walk l).toSubgraph) ∧
      NormalTrailSystem.owner S (Sum.inl b) = NormalTrailSystem.owner S (Sum.inr ⟨b,Set.mem_univ _⟩) := by
  classical
  have hn : s(b,c) ∉ p.edges := by
    intro he
    have hi' : Sym2.map Sum.inl s(b,c) ∈ (T.walk i).toSubgraph.edgeSet := by
      rw [hi,leafWalk_edges]
      exact Or.inl ⟨s(b,c),p.mem_edges_toSubgraph.mpr he,rfl⟩
    have hj' : Sym2.map Sum.inl s(b,c) ∈ (T.walk j).toSubgraph.edgeSet := by
      rw [hj,leafWalk_edges]
      exact Or.inl ⟨s(b,c),by simp,rfl⟩
    exact Set.disjoint_left.mp (T.disjoint hij) hi' hj'
  obtain ⟨hP,hQ,hd,hu,hcount⟩ := pendant_transfer_data p hp h hn
  let P := (leafWalk (p.concat h)).copy hai.symm hbj.symm
  let Q := (leafWalk (Walk.nil : G.Walk b b)).copy haj.symm hbi.symm
  have heP : P.toSubgraph = (leafWalk (p.concat h)).toSubgraph := NormalTrailSystem.walk_copy_subgraph _ _ _
  have heQ : Q.toSubgraph = (leafWalk (Walk.nil : G.Walk b b)).toSubgraph := NormalTrailSystem.walk_copy_subgraph _ _ _
  obtain ⟨S,hSi,hSj,hSl,hSa,hSb,hs⟩ := replace_two_finishes_tracked T i j hij P Q
    (by simpa only [P,Walk.isTrail_copy] using hP)
    (by simpa only [Q,Walk.isTrail_copy] using hQ)
    (by rw [heP,heQ]; exact hd)
    (by rw [heP,heQ,hi,hj]; exact hu)
  rw [hi,hj,heP,heQ] at hs
  refine ⟨S,by omega,hSi.trans heP,hSj.trans heQ,hSl,?_⟩
  have hstart : Sum.inl b = S.start j := by rw [hSa,haj]
  have hfinish : Sum.inr ⟨b,Set.mem_univ _⟩ = S.finish j := by
    simp [hSb,hbi]
  exact ((NormalTrailSystem.endpoint_iff_owner S _ j).mp (Or.inl hstart)).trans
    ((NormalTrailSystem.endpoint_iff_owner S _ j).mp (Or.inr hfinish)).symm

end Erdos583DefectTransportDevelopment
