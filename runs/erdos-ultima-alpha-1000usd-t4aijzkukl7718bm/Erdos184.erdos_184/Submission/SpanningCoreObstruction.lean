import Submission.RigidityDegree

/-! A proper connected spanning subgraph can remain a rigid minimal core.
This rules out a support-rank induction shortcut, not Erdős 184. -/

open SimpleGraph
open scoped Classical
namespace Erdos184Work.SpanningCoreObstruction
open Critical EvenCore Rigidity RainbowCore
set_option maxHeartbeats 3000000

abbrev residual : SimpleGraph (Fin 7) :=
  graph \ triangle.toSubgraph.spanningCoe

lemma base_rigid : CycleRigid graph := by
  refine rigid_of_saturated_evenMinimal ?_ graph_minimal_and_number.1 1 ?_
  · simpa only [← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using graph_even
  · rw [graph_minimal_and_number.2]
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using graph_degree_one

lemma residual_even : ∀ v, Even (residual.degree v) := by
  have h := delete_cycle_even (G := graph) (by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using graph_even) triangle_isCycle
  simpa only [← SimpleGraph.card_neighborSet_eq_degree,
    ← Nat.card_eq_fintype_card] using h

lemma residual_rigid : CycleRigid residual := by
  apply base_rigid.mono (by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using graph_even) sdiff_le
  simpa only [← SimpleGraph.card_neighborSet_eq_degree,
    ← Nat.card_eq_fintype_card] using residual_even

lemma residual_minimal : EvenMinimal residual := by
  apply residual_rigid.evenMinimal
  simpa only [← SimpleGraph.card_neighborSet_eq_degree,
    ← Nat.card_eq_fintype_card] using residual_even

lemma residual_connected : residual.Connected := by
  have h := triangle_nonseparating
  change (graph.deleteEdges triangle.toSubgraph.spanningCoe.edgeSet).Connected at h
  simpa only [SimpleGraph.deleteEdges_edgeSet] using h

lemma residual_number : number residual = 2 := by
  have h := (graph_minimal_and_number.1.cycleCritical (by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using graph_even)) 0 triangle triangle_isCycle
  rw [graph_minimal_and_number.2] at h
  change 3 = number residual + 1 at h
  omega

lemma residual_proper : residual.edgeFinset.card < graph.edgeFinset.card := by
  simpa only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card]
    using delete_cycle_card_lt triangle_isCycle

lemma residual_support : residual.support = graph.support := by
  rw [residual_connected.preconnected.support_eq_univ,
    graph_connected.preconnected.support_eq_univ]

/-- The decomposition number can increase under a connected spanning
extension even when both graphs are rigid minimal cores. -/
lemma nested_spanning_rigid_cores :
    ∃ G R : SimpleGraph (Fin 7),
      (∀ v, Even (G.degree v)) ∧ (∀ v, Even (R.degree v)) ∧
      CycleRigid G ∧ CycleRigid R ∧ EvenMinimal G ∧ EvenMinimal R ∧
      G.Connected ∧ R.Connected ∧ R ≤ G ∧ R.support = G.support ∧
      R.edgeFinset.card < G.edgeFinset.card ∧
      number R = 2 ∧ number G = 3 := by
  refine ⟨graph,residual,?_,?_,base_rigid,residual_rigid,
    graph_minimal_and_number.1,residual_minimal,graph_connected,
    residual_connected,sdiff_le,residual_support,?_,
    residual_number,graph_minimal_and_number.2⟩
  · simpa only [← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using graph_even
  · simpa only [← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using residual_even
  · simpa only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card]
      using residual_proper

#print axioms nested_spanning_rigid_cores
end Erdos184Work.SpanningCoreObstruction
