import Submission.TriangleCertificate

/-! A checked finite member of the triangle-sensitivity family.
This is not a counterexample to Erdős 184. -/
set_option maxRecDepth 4000
set_option maxHeartbeats 400000
open SimpleGraph
namespace Erdos184.TriangleSensitivityFinite
open CycleNumberSubmodularity

abbrev V := Fin 23

def neighbors : V → List V := ![[1,2,7,8,9,11],[0,2,3,4,5,6],[0,1,3,4,5,6],[1,2,4,5,6,20],[1,2,3,5,6,18],[1,2,3,4,6,21],[1,2,3,4,5,22],[0,8,9,10,11,14],[0,7,9,10,12,13],[0,7,8,10,13,14],[7,8,9,11,12,16],[0,7,10,12,13,14],[8,10,11,13,14,17],[8,9,11,12,14,19],[7,9,11,12,13,15],[14,16,17,18,19,22],[10,15,17,18,20,21],[12,15,16,18,21,22],[4,15,16,17,19,20],[13,15,18,20,21,22],[3,16,18,19,21,22],[5,16,17,19,20,22],[6,15,17,19,20,21]]

def G : SimpleGraph V where
  Adj u v := v ∈ neighbors u
  symm := by
    change ∀ u v : V, v ∈ neighbors u → u ∈ neighbors v
    decide
  loopless := by
    change ∀ v : V, v ∉ neighbors v
    decide
instance : DecidableRel G.Adj := fun u v => inferInstanceAs (Decidable (v ∈ neighbors u))
attribute [irreducible] G

def c0 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 7) <|
  .cons (by decide : G.Adj 7 8) <|
  .cons (by decide : G.Adj 8 9) <|
  .cons (by decide : G.Adj 9 10) <|
  .cons (by decide : G.Adj 10 11) <|
  .cons (by decide : G.Adj 11 12) <|
  .cons (by decide : G.Adj 12 13) <|
  .cons (by decide : G.Adj 13 14) <|
  .cons (by decide : G.Adj 14 15) <|
  .cons (by decide : G.Adj 15 16) <|
  .cons (by decide : G.Adj 16 17) <|
  .cons (by decide : G.Adj 17 18) <|
  .cons (by decide : G.Adj 18 19) <|
  .cons (by decide : G.Adj 19 20) <|
  .cons (by decide : G.Adj 20 21) <|
  .cons (by decide : G.Adj 21 22) <|
  .cons (by decide : G.Adj 22 6) <|
  .cons (by decide : G.Adj 6 5) <|
  .cons (by decide : G.Adj 5 4) <|
  .cons (by decide : G.Adj 4 2) <|
  .cons (by decide : G.Adj 2 3) <|
  .cons (by decide : G.Adj 3 1) <|
  .cons (by decide : G.Adj 1 0) <|
  .nil
lemma c0_cycle : c0.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [c0],by decide⟩

def c1 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 9) <|
  .cons (by decide : G.Adj 9 7) <|
  .cons (by decide : G.Adj 7 10) <|
  .cons (by decide : G.Adj 10 8) <|
  .cons (by decide : G.Adj 8 13) <|
  .cons (by decide : G.Adj 13 11) <|
  .cons (by decide : G.Adj 11 14) <|
  .cons (by decide : G.Adj 14 12) <|
  .cons (by decide : G.Adj 12 17) <|
  .cons (by decide : G.Adj 17 15) <|
  .cons (by decide : G.Adj 15 18) <|
  .cons (by decide : G.Adj 18 16) <|
  .cons (by decide : G.Adj 16 21) <|
  .cons (by decide : G.Adj 21 19) <|
  .cons (by decide : G.Adj 19 22) <|
  .cons (by decide : G.Adj 22 20) <|
  .cons (by decide : G.Adj 20 3) <|
  .cons (by decide : G.Adj 3 4) <|
  .cons (by decide : G.Adj 4 6) <|
  .cons (by decide : G.Adj 6 1) <|
  .cons (by decide : G.Adj 1 5) <|
  .cons (by decide : G.Adj 5 2) <|
  .cons (by decide : G.Adj 2 0) <|
  .nil
lemma c1_cycle : c1.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [c1],by decide⟩

def c2 : G.Walk 1 1 :=
  .cons (by decide : G.Adj 1 4) <|
  .cons (by decide : G.Adj 4 18) <|
  .cons (by decide : G.Adj 18 20) <|
  .cons (by decide : G.Adj 20 16) <|
  .cons (by decide : G.Adj 16 10) <|
  .cons (by decide : G.Adj 10 12) <|
  .cons (by decide : G.Adj 12 8) <|
  .cons (by decide : G.Adj 8 0) <|
  .cons (by decide : G.Adj 0 11) <|
  .cons (by decide : G.Adj 11 7) <|
  .cons (by decide : G.Adj 7 14) <|
  .cons (by decide : G.Adj 14 9) <|
  .cons (by decide : G.Adj 9 13) <|
  .cons (by decide : G.Adj 13 19) <|
  .cons (by decide : G.Adj 19 15) <|
  .cons (by decide : G.Adj 15 22) <|
  .cons (by decide : G.Adj 22 17) <|
  .cons (by decide : G.Adj 17 21) <|
  .cons (by decide : G.Adj 21 5) <|
  .cons (by decide : G.Adj 5 3) <|
  .cons (by decide : G.Adj 3 6) <|
  .cons (by decide : G.Adj 6 2) <|
  .cons (by decide : G.Adj 2 1) <|
  .nil
lemma c2_cycle : c2.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [c2],by decide⟩

def walks : Fin 3 → Σ v, G.Walk v v := ![⟨0,c0⟩,⟨0,c1⟩,⟨1,c2⟩]

lemma walk_cycles : ∀ i, (walks i).2.IsCycle := by
  intro i
  fin_cases i
  · exact c0_cycle
  · exact c1_cycle
  · exact c2_cycle
lemma walk_disjoint : ∀ i j, i ≠ j → List.Disjoint (walks i).2.edges (walks j).2.edges := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    first | exact (hij rfl).elim | exact List.disjoint_of_nodup_append (by decide)
def e0 : List (Sym2 V) := [s(0,7),s(7,8),s(8,9),s(9,10),s(10,11),s(11,12),s(12,13),s(13,14),s(14,15),s(15,16),s(16,17),s(17,18),s(18,19),s(19,20),s(20,21),s(21,22),s(22,6),s(6,5),s(5,4),s(4,2),s(2,3),s(3,1),s(1,0)]
lemma c0_edges : c0.edges = e0 := rfl
def e1 : List (Sym2 V) := [s(0,9),s(9,7),s(7,10),s(10,8),s(8,13),s(13,11),s(11,14),s(14,12),s(12,17),s(17,15),s(15,18),s(18,16),s(16,21),s(21,19),s(19,22),s(22,20),s(20,3),s(3,4),s(4,6),s(6,1),s(1,5),s(5,2),s(2,0)]
lemma c1_edges : c1.edges = e1 := rfl
def e2 : List (Sym2 V) := [s(1,4),s(4,18),s(18,20),s(20,16),s(16,10),s(10,12),s(12,8),s(8,0),s(0,11),s(11,7),s(7,14),s(14,9),s(9,13),s(13,19),s(19,15),s(15,22),s(22,17),s(17,21),s(21,5),s(5,3),s(3,6),s(6,2),s(2,1)]
lemma c2_edges : c2.edges = e2 := rfl
set_option maxHeartbeats 4000000 in
lemma walk_cover : ∀ u v, G.Adj u v ↔ ∃ i, s(u,v) ∈ (walks i).2.edges := by
  intro u v
  simp only [Fin.exists_fin_succ,Fin.exists_fin_zero,or_false]
  change G.Adj u v ↔ s(u,v) ∈ c0.edges ∨ s(u,v) ∈ c1.edges ∨ s(u,v) ∈ c2.edges
  rw [c0_edges,c1_edges,c2_edges]
  revert u v
  decide +kernel

lemma degree : ∀ v, G.degree v = 6 := by intro v; fin_cases v <;> decide

def triangleEdges : Finset (Sym2 V) := {s(0,1),s(1,2),s(2,0)}
def T : SimpleGraph V := fromEdgeSet (triangleEdges : Set (Sym2 V))
def R : SimpleGraph V := G \ T
instance : DecidableRel T.Adj := by unfold T; infer_instance
instance : DecidableRel R.Adj := by unfold R; infer_instance
attribute [irreducible] T R

def triangle : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 1) <|
  .cons (by decide : G.Adj 1 2) <|
  .cons (by decide : G.Adj 2 0) .nil
lemma triangle_cycle : triangle.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [triangle],by decide⟩
lemma triangle_graph : triangle.toSubgraph.spanningCoe = T := by
  ext u v
  change (s(u,v) ∈ triangle.toSubgraph.edgeSet) ↔ T.Adj u v
  rw [Walk.mem_edges_toSubgraph]
  revert u v
  decide +kernel

def label : V → Fin 4 := ![0,3,3,3,3,3,3,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2]
def rep : Fin 4 → V := ![0,7,15,3]
lemma rep_right : Function.RightInverse rep label := by decide
lemma representative_degrees : (∑ j, R.degree (rep j)) = 22 := by decide

instance (j : Fin 4) : DecidableRel
    (RankCriticalPartitions.monochromatic R (OrderedCutBudget.threshold label j)).Adj :=
  fun u v => inferInstanceAs (Decidable (R.Adj u v ∧
    OrderedCutBudget.threshold label j u = OrderedCutBudget.threshold label j v))

lemma cut_cards (j : Fin 4) :
    (R \ RankCriticalPartitions.monochromatic R (OrderedCutBudget.threshold label j)).edgeFinset.card =
      if j = 0 then 0 else 4 := by
  simp only [R,edgeFinset_sdiff]
  fin_cases j <;> decide +kernel

open scoped Classical in
lemma variation_value : OrderedCutBudget.variation R label = 12 := by
  have hv (j : Fin 4) :
      (R.edgeSet \ (RankCriticalPartitions.monochromatic R (OrderedCutBudget.threshold label j)).edgeSet).ncard =
        if j = 0 then 0 else 4 := by
    simpa only [edgeFinset_card,← Nat.card_eq_fintype_card,Nat.card_coe_set_eq,edgeSet_sdiff]
      using cut_cards j
  unfold OrderedCutBudget.variation
  simp_rw [hv]
  decide
lemma T_edges : T.edgeFinset.card = 3 := by decide

open scoped Classical in
lemma certified : cycleNumber G = 3 ∧ G.IsEdgeConnected 6 ∧ R.IsEdgeConnected 4 ∧
    (∀ D : Finset R.Subgraph, TriangleCertificate.Pure R D → IsDecomposition R D →
      5 ≤ D.card) ∧
    (∀ D : Finset G.Subgraph, TriangleCertificate.Pure G D → IsDecomposition G D →
      triangle.toSubgraph ∈ D → 6 ≤ D.card) := by
  have hdeg (v : V) : Nat.card (G.neighborSet v) = 6 := by
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using degree v
  have ht : T.edgeSet.ncard ≤ 3 := by
    have h := T_edges
    simp only [edgeFinset_card,← Nat.card_eq_fintype_card,Nat.card_coe_set_eq] at h
    omega
  have hs : (∑ j, Nat.card ((G \ T).neighborSet (rep j))) = 22 := by
    simpa only [R,← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using representative_degrees
  have hv : OrderedCutBudget.variation (G \ T) label = 12 := by
    simpa only [R] using variation_value
  have h := TriangleCertificate.check G T walks walk_cycles walk_disjoint walk_cover
    hdeg triangle triangle_cycle triangle_graph ht label rep rep_right hs hv
  simpa only [R] using h

lemma optimum : cycleNumber G = 3 := certified.1
lemma G_edge_connected : G.IsEdgeConnected 6 := certified.2.1
lemma R_edge_connected : R.IsEdgeConnected 4 := certified.2.2.1

open scoped Classical in
lemma residual_lower (D : Finset R.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition R D) : 5 ≤ D.card := by
  simp only [IsRegularOfDegree,← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hc
  exact certified.2.2.2.1 D hc hd

open scoped Classical in
lemma forced_triangle_lower (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) (ht : triangle.toSubgraph ∈ D) : 6 ≤ D.card := by
  simp only [IsRegularOfDegree,← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hc
  exact certified.2.2.2.2 D hc hd ht

lemma G_even : ∀ v, Even (G.degree v) := by
  intro v
  rw [degree]
  decide
lemma R_even : ∀ v, Even (R.degree v) := by decide +kernel

end Erdos184.TriangleSensitivityFinite
