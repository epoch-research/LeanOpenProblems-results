import Submission.DoublePetersenGraph
import Submission.CriticalSaturation

/-! Identifying only degree-two vertices can destroy cycle-criticality.
The dense quotient below has a three-cycle partition. This is an auxiliary
obstruction to a proposed transformation, not a disproof of Erdos 184. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.PetersenIdentification
open Critical EvenCore
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

def edges : List (Sym2 (Fin 25)) := [s(0,10), s(1,10), s(0,23), s(1,23), s(0,11), s(4,11), s(0,24), s(4,24), s(0,12), s(5,12), s(0,14), s(5,14), s(1,13), s(2,13), s(1,22), s(2,22), s(1,14), s(6,14), s(1,21), s(6,21), s(2,15), s(3,15), s(2,11), s(3,11), s(2,16), s(7,16), s(2,19), s(7,19), s(3,17), s(4,17), s(3,10), s(4,10), s(3,18), s(8,18), s(3,16), s(8,16), s(4,19), s(9,19), s(4,20), s(9,20), s(5,20), s(7,20), s(5,18), s(7,18), s(5,21), s(8,21), s(5,13), s(8,13), s(6,22), s(8,22), s(6,15), s(8,15), s(6,23), s(9,23), s(6,17), s(9,17), s(7,24), s(9,24), s(7,12), s(9,12)]

def graph : SimpleGraph (Fin 25) := SimpleGraph.fromEdgeSet {e | e ∈ edges}
instance : DecidableRel graph.Adj := by unfold graph; infer_instance

lemma degree_table (v : Fin 25) : graph.degree v = if v.val < 10 then 6 else 4 := by
  fin_cases v <;> decide +kernel
lemma even (v : Fin 25) : Even (graph.degree v) := by
  rw [degree_table]
  split_ifs <;> decide
lemma degree_zero : graph.degree 0 = 6 := by simpa using degree_table 0
lemma degree_lower (v : Fin 25) : 4 ≤ graph.degree v := by
  rw [degree_table]
  split_ifs <;> omega
lemma edge_finset : graph.edgeFinset = edges.toFinset := by
  have hn : ∀ a : Fin 25, s(a,a) ∉ edges := by decide +kernel
  ext e
  induction e using Sym2.ind with
  | h a b =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, graph,
      SimpleGraph.fromEdgeSet_adj, Set.mem_setOf_eq, List.mem_toFinset]
    exact ⟨And.left, fun h => ⟨h, fun he => hn a (he.symm ▸ h)⟩⟩

lemma edge_card : graph.edgeFinset.card = 60 := by
  have hn : edges.Nodup := by simp [edges, Sym2.eq_iff]
  rw [edge_finset, List.toFinset_card_of_nodup hn]
  rfl

lemma adj_0_10 : graph.Adj 0 10 := by decide +kernel
lemma adj_0_11 : graph.Adj 0 11 := by decide +kernel
lemma adj_0_12 : graph.Adj 0 12 := by decide +kernel
lemma adj_1_13 : graph.Adj 1 13 := by decide +kernel
lemma adj_1_14 : graph.Adj 1 14 := by decide +kernel
lemma adj_1_22 : graph.Adj 1 22 := by decide +kernel
lemma adj_1_23 : graph.Adj 1 23 := by decide +kernel
lemma adj_10_1 : graph.Adj 10 1 := by decide +kernel
lemma adj_10_3 : graph.Adj 10 3 := by decide +kernel
lemma adj_11_2 : graph.Adj 11 2 := by decide +kernel
lemma adj_11_3 : graph.Adj 11 3 := by decide +kernel
lemma adj_12_7 : graph.Adj 12 7 := by decide +kernel
lemma adj_12_9 : graph.Adj 12 9 := by decide +kernel
lemma adj_13_1 : graph.Adj 13 1 := by decide +kernel
lemma adj_13_2 : graph.Adj 13 2 := by decide +kernel
lemma adj_13_8 : graph.Adj 13 8 := by decide +kernel
lemma adj_14_0 : graph.Adj 14 0 := by decide +kernel
lemma adj_14_5 : graph.Adj 14 5 := by decide +kernel
lemma adj_15_6 : graph.Adj 15 6 := by decide +kernel
lemma adj_15_8 : graph.Adj 15 8 := by decide +kernel
lemma adj_16_2 : graph.Adj 16 2 := by decide +kernel
lemma adj_16_3 : graph.Adj 16 3 := by decide +kernel
lemma adj_17_4 : graph.Adj 17 4 := by decide +kernel
lemma adj_17_6 : graph.Adj 17 6 := by decide +kernel
lemma adj_18_5 : graph.Adj 18 5 := by decide +kernel
lemma adj_18_8 : graph.Adj 18 8 := by decide +kernel
lemma adj_19_7 : graph.Adj 19 7 := by decide +kernel
lemma adj_19_9 : graph.Adj 19 9 := by decide +kernel
lemma adj_2_13 : graph.Adj 2 13 := by decide +kernel
lemma adj_2_15 : graph.Adj 2 15 := by decide +kernel
lemma adj_2_19 : graph.Adj 2 19 := by decide +kernel
lemma adj_2_22 : graph.Adj 2 22 := by decide +kernel
lemma adj_20_4 : graph.Adj 20 4 := by decide +kernel
lemma adj_20_7 : graph.Adj 20 7 := by decide +kernel
lemma adj_21_1 : graph.Adj 21 1 := by decide +kernel
lemma adj_21_5 : graph.Adj 21 5 := by decide +kernel
lemma adj_22_1 : graph.Adj 22 1 := by decide +kernel
lemma adj_22_2 : graph.Adj 22 2 := by decide +kernel
lemma adj_22_6 : graph.Adj 22 6 := by decide +kernel
lemma adj_23_0 : graph.Adj 23 0 := by decide +kernel
lemma adj_23_9 : graph.Adj 23 9 := by decide +kernel
lemma adj_24_0 : graph.Adj 24 0 := by decide +kernel
lemma adj_24_4 : graph.Adj 24 4 := by decide +kernel
lemma adj_3_15 : graph.Adj 3 15 := by decide +kernel
lemma adj_3_17 : graph.Adj 3 17 := by decide +kernel
lemma adj_3_18 : graph.Adj 3 18 := by decide +kernel
lemma adj_4_10 : graph.Adj 4 10 := by decide +kernel
lemma adj_4_11 : graph.Adj 4 11 := by decide +kernel
lemma adj_4_19 : graph.Adj 4 19 := by decide +kernel
lemma adj_5_12 : graph.Adj 5 12 := by decide +kernel
lemma adj_5_13 : graph.Adj 5 13 := by decide +kernel
lemma adj_5_20 : graph.Adj 5 20 := by decide +kernel
lemma adj_6_14 : graph.Adj 6 14 := by decide +kernel
lemma adj_6_21 : graph.Adj 6 21 := by decide +kernel
lemma adj_6_23 : graph.Adj 6 23 := by decide +kernel
lemma adj_7_16 : graph.Adj 7 16 := by decide +kernel
lemma adj_7_18 : graph.Adj 7 18 := by decide +kernel
lemma adj_7_24 : graph.Adj 7 24 := by decide +kernel
lemma adj_8_16 : graph.Adj 8 16 := by decide +kernel
lemma adj_8_21 : graph.Adj 8 21 := by decide +kernel
lemma adj_8_22 : graph.Adj 8 22 := by decide +kernel
lemma adj_9_17 : graph.Adj 9 17 := by decide +kernel
lemma adj_9_20 : graph.Adj 9 20 := by decide +kernel
lemma adj_9_24 : graph.Adj 9 24 := by decide +kernel

def cycle0 : graph.Walk 0 0 :=
  .cons adj_0_10 (.cons adj_10_1 (.cons adj_1_14 (.cons adj_14_5 (.cons adj_5_12 (.cons adj_12_7 (.cons adj_7_18 (.cons adj_18_8 (.cons adj_8_16 (.cons adj_16_2 (.cons adj_2_19 (.cons adj_19_9 (.cons adj_9_24 (.cons adj_24_4 (.cons adj_4_11 (.cons adj_11_3 (.cons adj_3_17 (.cons adj_17_6 (.cons adj_6_23 (.cons adj_23_0 (.nil))))))))))))))))))))
lemma cycle0_cycle : cycle0.IsCycle := by
  simp [cycle0, Walk.isCycle_def, Walk.isTrail_def]

def cycle1 : graph.Walk 0 0 :=
  .cons adj_0_11 (.cons adj_11_2 (.cons adj_2_13 (.cons adj_13_1 (.cons adj_1_23 (.cons adj_23_9 (.cons adj_9_17 (.cons adj_17_4 (.cons adj_4_10 (.cons adj_10_3 (.cons adj_3_15 (.cons adj_15_8 (.cons adj_8_22 (.cons adj_22_6 (.cons adj_6_21 (.cons adj_21_5 (.cons adj_5_20 (.cons adj_20_7 (.cons adj_7_24 (.cons adj_24_0 (.nil))))))))))))))))))))
lemma cycle1_cycle : cycle1.IsCycle := by
  simp [cycle1, Walk.isCycle_def, Walk.isTrail_def]

def cycle2 : graph.Walk 0 0 :=
  .cons adj_0_12 (.cons adj_12_9 (.cons adj_9_20 (.cons adj_20_4 (.cons adj_4_19 (.cons adj_19_7 (.cons adj_7_16 (.cons adj_16_3 (.cons adj_3_18 (.cons adj_18_5 (.cons adj_5_13 (.cons adj_13_8 (.cons adj_8_21 (.cons adj_21_1 (.cons adj_1_22 (.cons adj_22_2 (.cons adj_2_15 (.cons adj_15_6 (.cons adj_6_14 (.cons adj_14_0 (.nil))))))))))))))))))))
lemma cycle2_cycle : cycle2.IsCycle := by
  simp [cycle2, Walk.isCycle_def, Walk.isTrail_def]

end Erdos184Work.PetersenIdentification
