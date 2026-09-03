import Submission.FinitePathSearch

/-! A cycle with a missing path vertex need not be absorbable into two paths.
This is an auxiliary obstruction, not a counterexample to Gallai's conjecture. -/
namespace Erdos583MissingCycleVertexObstructionDevelopment
open SimpleGraph Erdos583Work Erdos583Work.TriangleAbsorption
open Erdos583FinitePathSearchDevelopment
open scoped Classical
set_option maxHeartbeats 12000000
set_option maxRecDepth 16384
set_option Elab.async false

abbrev edges : Finset (Sym2 (Fin 13)) :=
  {s(0,2),s(0,3),s(0,7),s(1,4),s(1,5),s(1,6),s(1,12),s(2,3),s(2,4),s(2,5),s(3,4),s(3,5),s(4,5),s(6,8),s(6,9),s(6,12),s(7,10),s(7,11),s(8,9),s(8,10),s(8,11),s(9,10),s(9,11),s(10,11)}
def G : SimpleGraph (Fin 13) := fromEdgeSet (edges : Set (Sym2 (Fin 13)))
instance : DecidableRel G.Adj := by unfold G; infer_instance

def cycle : G.Walk 12 12 := (Walk.cons (by decide : G.Adj 12 1) (Walk.cons (by decide : G.Adj 1 4) (Walk.cons (by decide : G.Adj 4 5) (Walk.cons (by decide : G.Adj 5 2) (Walk.cons (by decide : G.Adj 2 3) (Walk.cons (by decide : G.Adj 3 0) (Walk.cons (by decide : G.Adj 0 7) (Walk.cons (by decide : G.Adj 7 10) (Walk.cons (by decide : G.Adj 10 11) (Walk.cons (by decide : G.Adj 11 8) (Walk.cons (by decide : G.Adj 8 9) (Walk.cons (by decide : G.Adj 9 6) (Walk.cons (by decide : G.Adj 6 12) Walk.nil)))))))))))))

def path : G.Walk 0 7 := (Walk.cons (by decide : G.Adj 0 2) (Walk.cons (by decide : G.Adj 2 4) (Walk.cons (by decide : G.Adj 4 3) (Walk.cons (by decide : G.Adj 3 5) (Walk.cons (by decide : G.Adj 5 1) (Walk.cons (by decide : G.Adj 1 6) (Walk.cons (by decide : G.Adj 6 8) (Walk.cons (by decide : G.Adj 8 10) (Walk.cons (by decide : G.Adj 10 9) (Walk.cons (by decide : G.Adj 9 11) (Walk.cons (by decide : G.Adj 11 7) Walk.nil)))))))))))

lemma cycle_isCycle : cycle.IsCycle := by
  simp [cycle,Walk.cons_isCycle_iff,Walk.isPath_def]
lemma path_isPath : path.IsPath := by
  apply Walk.IsPath.mk'
  decide
lemma cycle_spanning : ∀ v : Fin 13, v ∈ cycle.support := by decide
lemma path_missing : (12 : Fin 13) ∉ path.support := by decide
lemma edge_disjoint : Disjoint cycle.toSubgraph.edgeSet path.toSubgraph.edgeSet := by
  rw [Set.disjoint_left]
  simp only [Walk.mem_edges_toSubgraph]
  decide
lemma edge_cover : cycle.toSubgraph.edgeSet ∪ path.toSubgraph.edgeSet=G.edgeSet := by
  ext e
  induction e using Sym2.ind with
  | h x y =>
    simp only [Set.mem_union,Walk.mem_edges_toSubgraph,mem_edgeSet]
    revert x y
    decide
lemma edge_card : G.edgeSet.ncard=24 := by
  have hh : G.edgeFinset.card=24 := by decide
  simpa only [←Set.ncard_coe_finset,coe_edgeFinset] using hh

def next : Fin 13 → List (Fin 13) := ![[2, 3, 7],[4, 5, 6, 12],[0, 3, 4, 5],[0, 2, 4, 5],[1, 2, 3, 5],[1, 2, 3, 4],[1, 8, 9, 12],[0, 10, 11],[6, 9, 10, 11],[6, 8, 10, 11],[7, 8, 9, 11],[7, 8, 9, 10],[1, 6]]

lemma next_complete : ∀ u v, G.Adj u v → v ∈ next u := by decide

lemma search_zero : search next 12 {12} 12 0=false := by decide
lemma search_seven : search next 12 {12} 12 7=false := by decide


end Erdos583MissingCycleVertexObstructionDevelopment
