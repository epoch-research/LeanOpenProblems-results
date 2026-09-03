import Submission.ParityDegreeLower

/-! A ten-vertex nested-neighborhood example. Its decomposition number is ten.
Global edge-minimality is NOT proved in this file, and this is not a disproof
of Erdős184. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.NestedDoubleStar
open Critical Compression ParityDegreeLower
set_option maxHeartbeats 500000
abbrev V := Fin 10

def edgeList : List (V × V) := [(0,1), (0,2), (0,3), (0,4), (0,5), (0,6), (0,7), (0,8), (0,9), (1,2), (1,3), (1,4), (1,5), (1,6), (1,7), (1,8), (1,9), (2,4), (2,5), (2,6), (3,7), (3,8), (3,9)]
def graph : SimpleGraph V := SimpleGraph.fromRel (fun x y => (x,y) ∈ edgeList)
instance : DecidableRel graph.Adj := by unfold graph; infer_instance

lemma degree_table : ∀ v : V, graph.degree v = if v.val < 2 then 9 else if v.val < 4 then 5 else 3 := by
  intro v
  fin_cases v <;> decide +kernel
lemma all_odd : ∀ v : V, Odd (graph.degree v) := by
  intro v
  rw [degree_table]
  split_ifs <;> decide

lemma nested : NestedAlongEdges graph := by
  have h : ∀ u v : V, graph.Adj u v → graph.degree v ≤ graph.degree u →
      ∀ w : V, w ≠ u → graph.Adj v w → graph.Adj u w := by decide +kernel
  simpa only [NestedAlongEdges,← SimpleGraph.card_neighborSet_eq_degree,
    ← Nat.card_eq_fintype_card] using h

lemma universals : ∀ u : V, u.val < 2 → ∀ v : V, v ≠ u → graph.Adj u v := by decide +kernel
lemma edge_between_nonuniversals :
    graph.Adj 2 4 ∧ ¬ graph.Adj 2 3 ∧ ¬ graph.Adj 4 3 := by decide +kernel

def A : Finset V := {0,1}
def B : Finset V := {4,5,6,7,8,9}
def O : Finset V := Finset.univ \ A
lemma card_A : A.card = 2 := by decide
lemma card_B : B.card = 6 := by decide
lemma card_O : O.card = 8 := by decide
lemma degree_sum_A : (∑ v ∈ A, graph.degree v) = 18 := by decide +kernel
lemma independent_B : ∀ u ∈ B, ∀ v ∈ B, ¬ graph.Adj u v := by decide +kernel
lemma disjoint_AO : Disjoint A O := by decide

lemma number_lower : 10 ≤ number graph := by
  obtain ⟨D,hD,hdec,hcard⟩ := exists_minimum graph
  have h := independent_odd_degree_bound D hD hdec A B O (by rw [card_A]; omega)
    disjoint_AO independent_B
    (fun v _ => by simpa only [← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using all_odd v)
    (fun v _ => by simpa only [← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using all_odd v)
  have hs := degree_sum_A
  simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at h hs
  rw [card_A,card_B,card_O,hs,hcard] at h
  omega

def cycle0 : graph.Walk 0 0 :=
  .cons (show graph.Adj 0 1 by decide) (.cons (show graph.Adj 1 6 by decide) (.cons (show graph.Adj 6 0 by decide) (.nil)))
lemma cycle0_cycle : cycle0.IsCycle := by
  simp [cycle0, Walk.isCycle_def, Walk.isTrail_def]

def cycle1 : graph.Walk 1 1 :=
  .cons (show graph.Adj 1 2 by decide) (.cons (show graph.Adj 2 4 by decide) (.cons (show graph.Adj 4 1 by decide) (.nil)))
lemma cycle1_cycle : cycle1.IsCycle := by
  simp [cycle1, Walk.isCycle_def, Walk.isTrail_def]

def cycle2 : graph.Walk 0 0 :=
  .cons (show graph.Adj 0 3 by decide) (.cons (show graph.Adj 3 1 by decide) (.cons (show graph.Adj 1 9 by decide) (.cons (show graph.Adj 9 0 by decide) (.nil))))
lemma cycle2_cycle : cycle2.IsCycle := by
  simp [cycle2, Walk.isCycle_def, Walk.isTrail_def]

def cycle3 : graph.Walk 0 0 :=
  .cons (show graph.Adj 0 2 by decide) (.cons (show graph.Adj 2 5 by decide) (.cons (show graph.Adj 5 1 by decide) (.cons (show graph.Adj 1 7 by decide) (.cons (show graph.Adj 7 3 by decide) (.cons (show graph.Adj 3 8 by decide) (.cons (show graph.Adj 8 0 by decide) (.nil)))))))
lemma cycle3_cycle : cycle3.IsCycle := by
  simp [cycle3, Walk.isCycle_def, Walk.isTrail_def]

def piece : Fin 10 → graph.Subgraph
  | 0 => cycle0.toSubgraph
  | 1 => cycle1.toSubgraph
  | 2 => cycle2.toSubgraph
  | 3 => cycle3.toSubgraph
  | 4 => graph.subgraphOfAdj (show graph.Adj 0 4 by decide)
  | 5 => graph.subgraphOfAdj (show graph.Adj 0 5 by decide)
  | 6 => graph.subgraphOfAdj (show graph.Adj 0 7 by decide)
  | 7 => graph.subgraphOfAdj (show graph.Adj 1 8 by decide)
  | 8 => graph.subgraphOfAdj (show graph.Adj 2 6 by decide)
  | 9 => graph.subgraphOfAdj (show graph.Adj 3 9 by decide)

def pieceEdges : Fin 10 → Finset (Sym2 V)
  | 0 => cycle0.edges.toFinset
  | 1 => cycle1.edges.toFinset
  | 2 => cycle2.edges.toFinset
  | 3 => cycle3.edges.toFinset
  | 4 => {s(0,4)}
  | 5 => {s(0,5)}
  | 6 => {s(0,7)}
  | 7 => {s(1,8)}
  | 8 => {s(2,6)}
  | 9 => {s(3,9)}

lemma piece_edges (i : Fin 10) : (piece i).edgeSet = (pieceEdges i : Set (Sym2 V)) := by
  fin_cases i
  · ext e
    simp only [piece,pieceEdges,Finset.mem_coe,List.mem_toFinset]
    exact cycle0.mem_edges_toSubgraph
  · ext e
    simp only [piece,pieceEdges,Finset.mem_coe,List.mem_toFinset]
    exact cycle1.mem_edges_toSubgraph
  · ext e
    simp only [piece,pieceEdges,Finset.mem_coe,List.mem_toFinset]
    exact cycle2.mem_edges_toSubgraph
  · ext e
    simp only [piece,pieceEdges,Finset.mem_coe,List.mem_toFinset]
    exact cycle3.mem_edges_toSubgraph
  all_goals simp [piece,pieceEdges,SimpleGraph.edgeSet_subgraphOfAdj]

lemma piece_property (i : Fin 10) : IsCycleOrEdge (piece i).coe := by
  fin_cases i
  · left
    simpa only [piece,SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using cycle_coe_regular graph cycle0_cycle
  · left
    simpa only [piece,SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using cycle_coe_regular graph cycle1_cycle
  · left
    simpa only [piece,SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using cycle_coe_regular graph cycle2_cycle
  · left
    simpa only [piece,SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using cycle_coe_regular graph cycle3_cycle
  all_goals exact CriticalExample.single_piece_property (by decide)

lemma piece_disjoint : ∀ i j : Fin 10, i ≠ j → Disjoint (pieceEdges i) (pieceEdges j) := by
  intro i
  fin_cases i <;> decide +kernel
lemma piece_cover : ∀ a b : V, graph.Adj a b ↔ ∃ i : Fin 10, s(a,b) ∈ pieceEdges i := by
  intro a
  fin_cases a <;> decide +kernel

lemma number_upper : number graph ≤ 10 := by
  have hd := finite_family_decomposition piece pieceEdges piece_edges piece_disjoint piece_cover
  have hn := number_le (Finset.univ.image piece) (by
    intro H hH
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hH
    exact piece_property i) hd
  have hc : (Finset.univ.image piece).card ≤ 10 :=
    Finset.card_image_le.trans (by simp)
  omega
lemma number_ten : number graph = 10 := Nat.le_antisymm number_upper number_lower

end Erdos184Work.NestedDoubleStar
#print axioms Erdos184Work.NestedDoubleStar.nested
#print axioms Erdos184Work.NestedDoubleStar.number_ten
