import Submission.Work

/-! A common-neighbor switch for a matched inactive-vertex proxy.
This is local surgery, not a global matching normalization theorem. -/
open SimpleGraph Erdos583Work Erdos583Work.RootedTailSystem
namespace Erdos583MatchingProxyDevelopment
open scoped Classical
set_option maxHeartbeats 1200000

/-- Exchange the first edges of two edge-disjoint trails entering the same
vertex. Each exchanged edge remains first, at its original outer endpoint,
in the other member. -/
lemma common_neighbor_switch {V : Type*} {G : SimpleGraph V} {r b x a c : V}
    (h : G.Adj r x) (g : G.Adj b x) (p : G.Walk x a) (q : G.Walk x c)
    (hp : (Walk.cons h p).IsTrail) (hq : (Walk.cons g q).IsTrail)
    (hd : Disjoint (Walk.cons h p).toSubgraph.edgeSet
      (Walk.cons g q).toSubgraph.edgeSet) :
    (Walk.cons g p).IsTrail ∧ (Walk.cons h q).IsTrail ∧
      Disjoint (Walk.cons g p).toSubgraph.edgeSet (Walk.cons h q).toSubgraph.edgeSet ∧
      (Walk.cons g p).toSubgraph.edgeSet ∪ (Walk.cons h q).toSubgraph.edgeSet =
        (Walk.cons h p).toSubgraph.edgeSet ∪ (Walk.cons g q).toSubgraph.edgeSet := by
  have eh : s(r,x) ∈ (Walk.cons h p).toSubgraph.edgeSet := by simp
  have eg : s(b,x) ∈ (Walk.cons g q).toSubgraph.edgeSet := by simp
  have hgp : s(b,x) ∉ p.edges := by
    intro hh
    apply Set.disjoint_left.mp hd _ eg
    simp only [Walk.mem_edges_toSubgraph, Walk.edges_cons, List.mem_cons]
    exact Or.inr hh
  have hhq : s(r,x) ∉ q.edges := by
    intro hh
    apply Set.disjoint_left.mp hd eh
    simp only [Walk.mem_edges_toSubgraph, Walk.edges_cons, List.mem_cons]
    exact Or.inr hh
  refine ⟨hp.of_cons.cons g hgp, hq.of_cons.cons h hhq, ?_, ?_⟩
  · apply Set.disjoint_left.mpr
    intro e he hf
    simp only [Walk.mem_edges_toSubgraph, Walk.edges_cons, List.mem_cons] at he hf
    rcases he with rfl | he <;> rcases hf with hf | hf
    · exact Set.disjoint_left.mp hd (hf ▸ eh) eg
    · exact (Walk.isTrail_cons g q).mp hq |>.2 hf
    · exact (Walk.isTrail_cons h p).mp hp |>.2 (hf ▸ he)
    · apply Set.disjoint_left.mp hd
      · simp only [Walk.mem_edges_toSubgraph, Walk.edges_cons, List.mem_cons]
        exact Or.inr he
      · simp only [Walk.mem_edges_toSubgraph, Walk.edges_cons, List.mem_cons]
        exact Or.inr hf
  · ext e
    simp only [Set.mem_union, Walk.mem_edges_toSubgraph, Walk.edges_cons, List.mem_cons]
    tauto

/-- If only the first member is defective and the root is absent from the
receiver's tail, this switch repairs the defect or moves it to the marked
edge's outer endpoint. The marked edge is still the first edge there. -/
lemma proxy_single_defect {V : Type*} {G : SimpleGraph V} {r b x a c : V}
    (h : G.Adj r x) (g : G.Adj b x) (p : G.Walk x a) (q : G.Walk x c)
    (hp : (Walk.cons h p).IsTrail) (hpPath : p.IsPath)
    (hq : (Walk.cons g q).IsPath) (hrq : r ∉ q.support)
    (hd : Disjoint (Walk.cons h p).toSubgraph.edgeSet
      (Walk.cons g q).toSubgraph.edgeSet) :
    (Walk.cons g p).IsTrail ∧ (Walk.cons h q).IsPath ∧
      Disjoint (Walk.cons g p).toSubgraph.edgeSet (Walk.cons h q).toSubgraph.edgeSet ∧
      (Walk.cons g p).toSubgraph.edgeSet ∪ (Walk.cons h q).toSubgraph.edgeSet =
        (Walk.cons h p).toSubgraph.edgeSet ∪ (Walk.cons g q).toSubgraph.edgeSet ∧
      ((Walk.cons g p).IsPath ↔ b ∉ p.support) := by
  obtain ⟨hgp, _, hd', he⟩ := common_neighbor_switch h g p q hp hq.isTrail hd
  refine ⟨hgp, (Walk.cons_isPath_iff h q).mpr ⟨hq.of_cons, hrq⟩, hd', he, ?_⟩
  simp only [Walk.cons_isPath_iff, hpPath, true_and]

/-- The common-neighbor switch preserves all endpoint quotas exactly. -/
lemma proxy_endpoint_quota {V : Type*} [DecidableEq V] (r b a c v : V) :
    (if b=v then 1 else 0) + (if a=v then 1 else 0) +
        ((if r=v then 1 else 0) + (if c=v then 1 else 0)) =
      (if r=v then 1 else 0) + (if a=v then 1 else 0) +
        ((if b=v then 1 else 0) + (if c=v then 1 else 0)) := by
  omega

/-- Exact incidence-score change in the one-defect switch: one if it repairs,
zero if the new initial vertex is repeated. There is no hidden score loss. -/
lemma proxy_single_defect_score {V : Type*} [Fintype V] {G : SimpleGraph V}
    {r b x a c : V} (h : G.Adj r x) (g : G.Adj b x)
    (p : G.Walk x a) (q : G.Walk x c)
    (hp : p.IsPath) (hrp : r ∈ p.support)
    (hq : (Walk.cons g q).IsPath) (hrq : r ∉ q.support) :
    (Walk.cons g p).toSubgraph.verts.ncard + (Walk.cons h q).toSubgraph.verts.ncard =
      (Walk.cons h p).toSubgraph.verts.ncard + (Walk.cons g q).toSubgraph.verts.ncard +
        if b ∈ p.support then 0 else 1 := by
  have hnew : (Walk.cons h q).IsPath :=
    (Walk.cons_isPath_iff h q).mpr ⟨hq.of_cons, hrq⟩
  have hlen : (Walk.cons h q).length = (Walk.cons g q).length := by simp
  rw [InducedBuffer.path_vertex_ncard _ hnew,
    InducedBuffer.path_vertex_ncard _ hq, hlen,
    MobileDefect.single_defect_score h p hp hrp]
  by_cases hb : b ∈ p.support
  · rw [if_pos hb, MobileDefect.single_defect_score g p hp hb]
    simp
  · have hgp : (Walk.cons g p).IsPath := (Walk.cons_isPath_iff g p).mpr ⟨hp, hb⟩
    rw [if_neg hb, InducedBuffer.path_vertex_ncard _ hgp]
    simp only [Walk.length_cons]
    omega

end Erdos583MatchingProxyDevelopment
