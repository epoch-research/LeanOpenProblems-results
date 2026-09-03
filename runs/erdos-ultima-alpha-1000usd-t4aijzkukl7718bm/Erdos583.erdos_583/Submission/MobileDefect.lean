import Submission.Work

/-! Transferring a single repeated-endpoint defect without imposing normal
endpoint multiplicity bounds at the moving root. -/
open SimpleGraph Erdos583Work Erdos583Work.TrailNormalization
namespace Erdos583MobileDefectDevelopment
open scoped Classical
set_option maxHeartbeats 1200000

/-- Two trails beginning at the same root can transfer the first edge of one
to the other in reverse. Both endpoints move to the neighbor. -/
lemma same_root_transfer_data {V : Type*} {G : SimpleGraph V} {r x b c : V}
    (h : G.Adj r x) (p : G.Walk x b) (q : G.Walk r c)
    (hp : (Walk.cons h p).IsTrail) (hq : q.IsTrail)
    (hd : Disjoint (Walk.cons h p).toSubgraph.edgeSet q.toSubgraph.edgeSet) :
    p.IsTrail ∧ (Walk.cons h.symm q).IsTrail ∧
      Disjoint p.toSubgraph.edgeSet (Walk.cons h.symm q).toSubgraph.edgeSet ∧
      p.toSubgraph.edgeSet ∪ (Walk.cons h.symm q).toSubgraph.edgeSet =
        (Walk.cons h p).toSubgraph.edgeSet ∪ q.toSubgraph.edgeSet := by
  have hp' := hp.of_cons
  have hEdge : s(r,x) ∈ (Walk.cons h p).toSubgraph.edgeSet := by simp
  have hEq : s(x,r) ∉ q.edges := by
    intro hh
    apply Set.disjoint_left.mp hd hEdge
    rw [Walk.mem_edges_toSubgraph,Sym2.eq_swap]
    exact hh
  have hq' := hq.cons h.symm hEq
  have hdpq : Disjoint p.toSubgraph.edgeSet q.toSubgraph.edgeSet := by
    apply hd.mono_left
    intro e he
    simp only [Walk.mem_edges_toSubgraph,Walk.edges_cons,List.mem_cons] at *
    exact Or.inr he
  have hpx : s(x,r) ∉ p.toSubgraph.edgeSet := by
    rw [Walk.mem_edges_toSubgraph,Sym2.eq_swap]
    exact (Walk.isTrail_cons h p).mp hp |>.2
  refine ⟨hp',hq',?_,?_⟩
  · apply Set.disjoint_left.mpr
    intro e he hf
    simp only [Walk.mem_edges_toSubgraph,Walk.edges_cons,List.mem_cons] at hf
    rcases hf with rfl | hf
    · exact hpx he
    · exact Set.disjoint_left.mp hdpq he ((q.mem_edges_toSubgraph).mpr hf)
  · ext e
    simp only [Set.mem_union,Walk.mem_edges_toSubgraph,Walk.edges_cons,List.mem_cons]
    rw [Sym2.eq_swap (a := x)]
    tauto

/-- If the donor has only its initial root repeated and the receiver is a path,
then transferring the first edge either repairs the defect or moves its unique
repetition to the neighbor. In the latter case BOTH vertex sets stay fixed. -/
lemma move_single_defect {V : Type*} {G : SimpleGraph V} {r x b c : V}
    (h : G.Adj r x) (p : G.Walk x b) (q : G.Walk r c)
    (hp : (Walk.cons h p).IsTrail) (hpPath : p.IsPath) (hr : r ∈ p.support)
    (hq : q.IsPath)
    (hd : Disjoint (Walk.cons h p).toSubgraph.edgeSet q.toSubgraph.edgeSet) :
    p.IsPath ∧ (Walk.cons h.symm q).IsTrail ∧
      Disjoint p.toSubgraph.edgeSet (Walk.cons h.symm q).toSubgraph.edgeSet ∧
      p.toSubgraph.edgeSet ∪ (Walk.cons h.symm q).toSubgraph.edgeSet =
        (Walk.cons h p).toSubgraph.edgeSet ∪ q.toSubgraph.edgeSet ∧
      p.toSubgraph.verts=(Walk.cons h p).toSubgraph.verts ∧
      ((Walk.cons h.symm q).IsPath ↔ x ∉ q.support) ∧
      (x ∈ q.support → (Walk.cons h.symm q).toSubgraph.verts=q.toSubgraph.verts) := by
  obtain ⟨_,ht,hd',he⟩ := same_root_transfer_data h p q hp hq.isTrail hd
  refine ⟨hpPath,ht,hd',he,?_,?_,?_⟩
  · rw [cons_verts,Set.insert_eq_of_mem ((p.mem_verts_toSubgraph).mpr hr)]
  · simp only [Walk.cons_isPath_iff,hq,true_and]
  · intro hx
    rw [cons_verts,Set.insert_eq_of_mem ((q.mem_verts_toSubgraph).mpr hx)]

/-- The endpoint multiplicity change is exactly minus two at the old root and
plus two at the new one, regardless of the finishing endpoints. This identity
also covers closed defective members. -/
lemma endpoint_quota_transfer {V : Type*} [DecidableEq V] (r x b c v : V) :
    (if x=v then 1 else 0) + (if b=v then 1 else 0) +
        ((if x=v then 1 else 0) + (if c=v then 1 else 0)) + 2*(if r=v then 1 else 0) =
      (if r=v then 1 else 0) + (if b=v then 1 else 0) +
        ((if r=v then 1 else 0) + (if c=v then 1 else 0)) + 2*(if x=v then 1 else 0) := by
  omega

/-- A nonempty root cycle inside a one-defect trail has simple tail. This is a
convenient score identity: exactly one vertex occurrence is redundant. -/
lemma single_defect_score {V : Type*} [Fintype V] {G : SimpleGraph V} {r x b : V}
    (h : G.Adj r x) (p : G.Walk x b) (hp : p.IsPath) (hr : r ∈ p.support) :
    (Walk.cons h p).toSubgraph.verts.ncard=(Walk.cons h p).length := by
  rw [cons_ncard_of_mem h p hr,Walk.length_cons]
  exact InducedBuffer.path_vertex_ncard p hp

end Erdos583MobileDefectDevelopment
