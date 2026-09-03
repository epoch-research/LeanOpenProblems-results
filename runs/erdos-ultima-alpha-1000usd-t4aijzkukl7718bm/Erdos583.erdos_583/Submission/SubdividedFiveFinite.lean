import Submission.CyclePredecessorConstraint

/-! Three exact five-cycle/six-cycle partitions of a subdivided complete graph on five vertices. -/
namespace Erdos583SubdividedFiveFiniteDevelopment
open SimpleGraph
set_option maxHeartbeats 3000000
set_option Elab.async false

def base : SimpleGraph (Fin 6) := fromEdgeSet
  {s(0,1),s(0,2),s(0,3),s(0,4),s(1,2),s(1,3),s(1,4),s(2,3),s(2,5),s(3,4),s(4,5)}

instance : DecidableRel base.Adj := by unfold base; infer_instance

def long0 : base.Walk 0 0 := Walk.cons (show base.Adj 0 1 by decide) (Walk.cons (show base.Adj 1 2 by decide) (Walk.cons (show base.Adj 2 5 by decide) (Walk.cons (show base.Adj 5 4 by decide) (Walk.cons (show base.Adj 4 3 by decide) (Walk.cons (show base.Adj 3 0 by decide) ((Walk.nil : base.Walk 0 0)))))))

def short0 : base.Walk 0 0 := Walk.cons (show base.Adj 0 4 by decide) (Walk.cons (show base.Adj 4 1 by decide) (Walk.cons (show base.Adj 1 3 by decide) (Walk.cons (show base.Adj 3 2 by decide) (Walk.cons (show base.Adj 2 0 by decide) ((Walk.nil : base.Walk 0 0))))))

lemma long0_cycle : long0.IsCycle := by simp [long0,Walk.cons_isCycle_iff,Walk.isPath_def]
lemma short0_cycle : short0.IsCycle := by simp [short0,Walk.cons_isCycle_iff,Walk.isPath_def]
lemma short0_length : short0.length=5 := rfl
lemma long0_spanning : ∀ u : Fin 6, u ∈ long0.support := by decide
lemma pair0_disjoint : Disjoint short0.toSubgraph.edgeSet long0.toSubgraph.edgeSet := by
  rw [Set.disjoint_left]
  simp only [Walk.mem_edges_toSubgraph]
  decide
lemma pair0_cover : short0.toSubgraph.edgeSet ∪ long0.toSubgraph.edgeSet=base.edgeSet := by
  ext e
  induction e using Sym2.ind with
  | h u v =>
    revert u v
    simp only [Set.mem_union,Walk.mem_edges_toSubgraph,mem_edgeSet]
    decide

def long1 : base.Walk 0 0 := Walk.cons (show base.Adj 0 1 by decide) (Walk.cons (show base.Adj 1 3 by decide) (Walk.cons (show base.Adj 3 2 by decide) (Walk.cons (show base.Adj 2 5 by decide) (Walk.cons (show base.Adj 5 4 by decide) (Walk.cons (show base.Adj 4 0 by decide) ((Walk.nil : base.Walk 0 0)))))))

def short1 : base.Walk 0 0 := Walk.cons (show base.Adj 0 3 by decide) (Walk.cons (show base.Adj 3 4 by decide) (Walk.cons (show base.Adj 4 1 by decide) (Walk.cons (show base.Adj 1 2 by decide) (Walk.cons (show base.Adj 2 0 by decide) ((Walk.nil : base.Walk 0 0))))))

lemma long1_cycle : long1.IsCycle := by simp [long1,Walk.cons_isCycle_iff,Walk.isPath_def]
lemma short1_cycle : short1.IsCycle := by simp [short1,Walk.cons_isCycle_iff,Walk.isPath_def]
lemma short1_length : short1.length=5 := rfl
lemma long1_spanning : ∀ u : Fin 6, u ∈ long1.support := by decide
lemma pair1_disjoint : Disjoint short1.toSubgraph.edgeSet long1.toSubgraph.edgeSet := by
  rw [Set.disjoint_left]
  simp only [Walk.mem_edges_toSubgraph]
  decide
lemma pair1_cover : short1.toSubgraph.edgeSet ∪ long1.toSubgraph.edgeSet=base.edgeSet := by
  ext e
  induction e using Sym2.ind with
  | h u v =>
    revert u v
    simp only [Set.mem_union,Walk.mem_edges_toSubgraph,mem_edgeSet]
    decide

def long2 : base.Walk 0 0 := Walk.cons (show base.Adj 0 2 by decide) (Walk.cons (show base.Adj 2 5 by decide) (Walk.cons (show base.Adj 5 4 by decide) (Walk.cons (show base.Adj 4 1 by decide) (Walk.cons (show base.Adj 1 3 by decide) (Walk.cons (show base.Adj 3 0 by decide) ((Walk.nil : base.Walk 0 0)))))))

def short2 : base.Walk 0 0 := Walk.cons (show base.Adj 0 1 by decide) (Walk.cons (show base.Adj 1 2 by decide) (Walk.cons (show base.Adj 2 3 by decide) (Walk.cons (show base.Adj 3 4 by decide) (Walk.cons (show base.Adj 4 0 by decide) ((Walk.nil : base.Walk 0 0))))))

lemma long2_cycle : long2.IsCycle := by simp [long2,Walk.cons_isCycle_iff,Walk.isPath_def]
lemma short2_cycle : short2.IsCycle := by simp [short2,Walk.cons_isCycle_iff,Walk.isPath_def]
lemma short2_length : short2.length=5 := rfl
lemma long2_spanning : ∀ u : Fin 6, u ∈ long2.support := by decide
lemma pair2_disjoint : Disjoint short2.toSubgraph.edgeSet long2.toSubgraph.edgeSet := by
  rw [Set.disjoint_left]
  simp only [Walk.mem_edges_toSubgraph]
  decide
lemma pair2_cover : short2.toSubgraph.edgeSet ∪ long2.toSubgraph.edgeSet=base.edgeSet := by
  ext e
  induction e using Sym2.ind with
  | h u v =>
    revert u v
    simp only [Set.mem_union,Walk.mem_edges_toSubgraph,mem_edgeSet]
    decide

lemma every_edge_in_long : ∀ u v : Fin 6, base.Adj u v →
    s(u,v) ∈ long0.toSubgraph.edgeSet ∨ s(u,v) ∈ long1.toSubgraph.edgeSet ∨ s(u,v) ∈ long2.toSubgraph.edgeSet := by
  simp only [Walk.mem_edges_toSubgraph]
  decide

lemma ordinary_complement : ∀ v w : Fin 6, (v=0 ∨ v=1 ∨ v=3) → v ≠ w → ¬base.Adj w v → w=5 := by decide

lemma tip_complement_left : ∀ w : Fin 6, w ≠ 2 → ¬base.Adj w 2 → w=4 := by decide
lemma tip_complement_right : ∀ w : Fin 6, w ≠ 4 → ¬base.Adj w 4 → w=2 := by decide

lemma ordinary_neighbor_pair : ∀ u : Fin 6, u ≠ 5 →
    ∃ v w : Fin 6, v ≠ w ∧ base.Adj u v ∧ base.Adj u w ∧
      (v=0 ∨ v=1 ∨ v=3) ∧ (w=0 ∨ w=1 ∨ w=3) := by decide

end Erdos583SubdividedFiveFiniteDevelopment
