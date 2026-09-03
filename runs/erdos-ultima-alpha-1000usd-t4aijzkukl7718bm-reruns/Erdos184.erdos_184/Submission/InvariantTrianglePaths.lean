import Submission.InvariantHajos

/-!
A path restriction imposed by an invariant even graph near a triangle.
This is a restricted-class structural lemma, not a fractional rounding theorem
or a settlement of the cycle-decomposition conjecture.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184.InvariantTrianglePaths
variable {V : Type*} [Fintype V] {G : SimpleGraph V}
set_option maxHeartbeats 800000

omit [Fintype V] in
/-- Close a simple path using two edges through an avoided vertex. -/
lemma two_spoke_cycle {v a b : V} (hva : G.Adj v a) (hvb : G.Adj v b)
    (hab : a ≠ b) (p : G.Walk a b) (hp : p.IsPath) (hv : v ∉ p.support) :
    (Walk.cons hva (p.concat hvb.symm)).IsCycle := by
  have hq : (p.concat hvb.symm).IsPath := by
    rw [Walk.isPath_def, Walk.support_concat]
    exact hp.support_nodup.concat hv
  apply (Walk.cons_isCycle_iff _ _).mpr
  refine ⟨hq, ?_⟩
  simp only [Walk.edges_concat, List.concat_eq_append, List.mem_append,
    List.mem_singleton]
  rintro (he | he)
  · exact hv (p.fst_mem_support_of_mem_edges he)
  · rcases Sym2.eq_iff.mp he with h | h
    · exact hva.ne h.2.symm
    · exact hab h.2

/-- Two edge-disjoint terminal paths avoiding the edges and third vertex of
an existing triangle have no common internal vertex in an invariant graph. -/
lemma paths_intersect_only_at_ends
    (he : ∀ x, Even (G.degree x)) (hi : InvariantPartitions.HasInvariantCount G)
    {v a b : V} (hva : G.Adj v a) (hvb : G.Adj v b) (hab : G.Adj a b)
    (p q : G.Walk a b) (hp : p.IsPath) (hq : q.IsPath)
    (hvp : v ∉ p.support) (hvq : v ∉ q.support)
    (habp : s(a,b) ∉ p.edges) (habq : s(a,b) ∉ q.edges)
    (hpq : p.edges.Disjoint q.edges) :
    ∀ x, x ∈ p.support → x ∈ q.support → x = a ∨ x = b := by
  let c := Walk.cons hva (p.concat hvb.symm)
  let d := Walk.cons hab q.reverse
  have hc : c.IsCycle := two_spoke_cycle hva hvb hab.ne p hp hvp
  have hd : d.IsCycle := by
    apply (Walk.cons_isCycle_iff _ _).mpr
    exact ⟨hq.reverse, by simpa only [Walk.edges_reverse,List.mem_reverse] using habq⟩
  have hdis : Disjoint c.toSubgraph.edgeSet d.toSubgraph.edgeSet := by
    apply Set.disjoint_left.mpr
    intro e hec hed
    have hec' : e ∈ c.edges := (c.mem_edges_toSubgraph).mp hec
    have hed' : e ∈ d.edges := (d.mem_edges_toSubgraph).mp hed
    simp only [c,d,Walk.edges_cons,Walk.edges_concat,List.concat_eq_append,
      List.mem_cons,List.mem_append,List.not_mem_nil,or_false,Walk.edges_reverse,
      List.mem_reverse] at hec' hed'
    rcases hec' with rfl | hec'
    · rcases hed' with h | h
      · rcases Sym2.eq_iff.mp h with hh | hh
        · exact hva.ne hh.1
        · exact hvb.ne hh.1
      · exact hvq (q.fst_mem_support_of_mem_edges h)
    · rcases hec' with h | rfl
      · rcases hed' with rfl | h'
        · exact habp h
        · exact hpq h h'
      · rcases hed' with h | h
        · rcases Sym2.eq_iff.mp h with hh | hh
          · exact hab.ne hh.1.symm
          · exact hva.ne hh.2
        · exact hvq (q.snd_mem_support_of_mem_edges h)
  have hbnd := hi.intersection_le_two he c.toSubgraph d.toSubgraph
    (cycle_subgraph_regular G hc) (cycle_subgraph_regular G hd) hdis
  intro x hxp hxq
  by_contra! hx
  have ha : a ∈ c.toSubgraph.verts ∩ d.toSubgraph.verts := by
    constructor
    · apply c.mem_verts_toSubgraph.mpr
      simp only [c,Walk.support_cons,Walk.support_concat,List.mem_cons,
        List.concat_eq_append,List.mem_append]
      exact Or.inr (Or.inl p.start_mem_support)
    · exact d.mem_verts_toSubgraph.mpr d.start_mem_support
  have hb : b ∈ c.toSubgraph.verts ∩ d.toSubgraph.verts := by
    constructor
    · apply c.mem_verts_toSubgraph.mpr
      simp only [c,Walk.support_cons,Walk.support_concat,List.mem_cons,
        List.concat_eq_append,List.mem_append]
      exact Or.inr (Or.inl p.end_mem_support)
    · apply d.mem_verts_toSubgraph.mpr
      simp only [d,Walk.support_cons,Walk.support_reverse,List.mem_cons,
        List.mem_reverse]
      exact Or.inr q.end_mem_support
  have hxx : x ∈ c.toSubgraph.verts ∩ d.toSubgraph.verts := by
    constructor
    · apply c.mem_verts_toSubgraph.mpr
      simp only [c,Walk.support_cons,Walk.support_concat,List.mem_cons,
        List.concat_eq_append,List.mem_append]
      exact Or.inr (Or.inl hxp)
    · apply d.mem_verts_toSubgraph.mpr
      simp only [d,Walk.support_cons,Walk.support_reverse,List.mem_cons,
        List.mem_reverse]
      exact Or.inr hxq
  have hsub : ({a,b,x} : Finset V) ⊆ (c.toSubgraph.verts ∩ d.toSubgraph.verts).toFinset := by
    intro y hy
    simp only [Finset.mem_insert,Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl
    · exact Set.mem_toFinset.mpr ha
    · exact Set.mem_toFinset.mpr hb
    · exact Set.mem_toFinset.mpr hxx
  have hcard : ({a,b,x} : Finset V).card = 3 := by
    simp [hab.ne,hx.1.symm,hx.2.symm]
  have hle := Finset.card_le_card hsub
  rw [hcard,← Set.ncard_eq_toFinset_card'] at hle
  omega

/-- The residual-graph formulation: isolate the third vertex and remove the
opposite edge. It applies in particular to the degree-two suppression case. -/
lemma residual_paths_intersect_only_at_ends
    (he : ∀ x, Even (G.degree x)) (hi : InvariantPartitions.HasInvariantCount G)
    {v a b : V} (hva : G.Adj v a) (hvb : G.Adj v b) (hab : G.Adj a b)
    {A : SimpleGraph V} (hA : A ≤ G.deleteIncidenceSet v) (hnab : ¬A.Adj a b)
    (p q : A.Walk a b) (hp : p.IsPath) (hq : q.IsPath)
    (hpq : p.edges.Disjoint q.edges) :
    ∀ x, x ∈ p.support → x ∈ q.support → x = a ∨ x = b := by
  let hAG : A ≤ G := hA.trans (G.deleteIncidenceSet_le v)
  have hav (r : A.Walk a b) : v ∉ r.support := by
    intro hv
    have hr : A.Reachable a v := (r.takeUntil v hv).reachable
    obtain ⟨w,hw⟩ := mem_support_of_reachable hva.ne hr.symm
    exact (deleteIncidenceSet_adj.mp (hA hw)).2.1 rfl
  have hn (r : A.Walk a b) : s(a,b) ∉ r.edges := by
    intro hr
    exact hnab (r.adj_of_mem_edges hr)
  have hh := paths_intersect_only_at_ends he hi hva hvb hab
    (p.mapLe hAG) (q.mapLe hAG) (hp.mapLe hAG) (hq.mapLe hAG)
    (by simpa only [Walk.support_mapLe_eq_support] using hav p)
    (by simpa only [Walk.support_mapLe_eq_support] using hav q)
    (by simpa only [Walk.edges_mapLe_eq_edges] using hn p)
    (by simpa only [Walk.edges_mapLe_eq_edges] using hn q)
    (by simpa only [Walk.edges_mapLe_eq_edges] using hpq)
  simpa only [Walk.support_mapLe_eq_support] using hh

end Erdos184.InvariantTrianglePaths
