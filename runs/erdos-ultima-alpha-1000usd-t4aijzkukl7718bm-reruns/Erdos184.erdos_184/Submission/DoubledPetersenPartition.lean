import Submission.DoubledPetersenSimple
import Submission.CountCritical

/-! An actual minimum five-cycle decomposition of the 25-vertex simple graph.
This is an auxiliary certificate, not a settlement of Erdős 184. -/
open SimpleGraph
open scoped Classical BigOperators
namespace Erdos184.DoubledPetersenSimple
open CycleNumberSubmodularity
set_option maxHeartbeats 500000
set_option maxRecDepth 20000

def partWalk0 : G.Walk 0 0 :=
  .cons (show G.Adj 0 1 from edge_mem 0 0) <|
  .cons (show G.Adj 1 2 from edge_mem 3 0) <|
  .cons (show G.Adj 2 3 from edge_mem 5 0) <|
  .cons (show G.Adj 3 4 from edge_mem 7 0) <|
  .cons (show G.Adj 4 0 from (show G.Adj 0 4 from edge_mem 1 0).symm) .nil
lemma partWalk0_cycle : partWalk0.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [partWalk0],by decide⟩

def partWalk1 : G.Walk 0 0 :=
  .cons (show G.Adj 0 5 from edge_mem 2 0) <|
  .cons (show G.Adj 5 8 from edge_mem 11 0) <|
  .cons (show G.Adj 8 3 from (show G.Adj 3 8 from edge_mem 8 0).symm) <|
  .cons (show G.Adj 3 17 from edge_mem 7 1) <|
  .cons (show G.Adj 17 4 from edge_mem 7 2) <|
  .cons (show G.Adj 4 9 from edge_mem 9 0) <|
  .cons (show G.Adj 9 7 from (show G.Adj 7 9 from edge_mem 14 0).symm) <|
  .cons (show G.Adj 7 2 from (show G.Adj 2 7 from edge_mem 6 0).symm) <|
  .cons (show G.Adj 2 13 from (show G.Adj 13 2 from edge_mem 3 2).symm) <|
  .cons (show G.Adj 13 1 from (show G.Adj 1 13 from edge_mem 3 1).symm) <|
  .cons (show G.Adj 1 10 from (show G.Adj 10 1 from edge_mem 0 2).symm) <|
  .cons (show G.Adj 10 0 from (show G.Adj 0 10 from edge_mem 0 1).symm) .nil
lemma partWalk1_cycle : partWalk1.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [partWalk1],by decide⟩

def partWalk2 : G.Walk 0 0 :=
  .cons (show G.Adj 0 11 from edge_mem 1 1) <|
  .cons (show G.Adj 11 4 from edge_mem 1 2) <|
  .cons (show G.Adj 4 19 from edge_mem 9 1) <|
  .cons (show G.Adj 19 9 from edge_mem 9 2) <|
  .cons (show G.Adj 9 6 from (show G.Adj 6 9 from edge_mem 13 0).symm) <|
  .cons (show G.Adj 6 8 from edge_mem 12 0) <|
  .cons (show G.Adj 8 18 from (show G.Adj 18 8 from edge_mem 8 2).symm) <|
  .cons (show G.Adj 18 3 from (show G.Adj 3 18 from edge_mem 8 1).symm) <|
  .cons (show G.Adj 3 15 from (show G.Adj 15 3 from edge_mem 5 2).symm) <|
  .cons (show G.Adj 15 2 from (show G.Adj 2 15 from edge_mem 5 1).symm) <|
  .cons (show G.Adj 2 16 from edge_mem 6 1) <|
  .cons (show G.Adj 16 7 from edge_mem 6 2) <|
  .cons (show G.Adj 7 5 from (show G.Adj 5 7 from edge_mem 10 0).symm) <|
  .cons (show G.Adj 5 12 from (show G.Adj 12 5 from edge_mem 2 2).symm) <|
  .cons (show G.Adj 12 0 from (show G.Adj 0 12 from edge_mem 2 1).symm) .nil
lemma partWalk2_cycle : partWalk2.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [partWalk2],by decide⟩

def partWalk3 : G.Walk 5 5 :=
  .cons (show G.Adj 5 20 from edge_mem 10 1) <|
  .cons (show G.Adj 20 7 from edge_mem 10 2) <|
  .cons (show G.Adj 7 24 from edge_mem 14 1) <|
  .cons (show G.Adj 24 9 from edge_mem 14 2) <|
  .cons (show G.Adj 9 23 from (show G.Adj 23 9 from edge_mem 13 2).symm) <|
  .cons (show G.Adj 23 6 from (show G.Adj 6 23 from edge_mem 13 1).symm) <|
  .cons (show G.Adj 6 22 from edge_mem 12 1) <|
  .cons (show G.Adj 22 8 from edge_mem 12 2) <|
  .cons (show G.Adj 8 21 from (show G.Adj 21 8 from edge_mem 11 2).symm) <|
  .cons (show G.Adj 21 5 from (show G.Adj 5 21 from edge_mem 11 1).symm) .nil
lemma partWalk3_cycle : partWalk3.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [partWalk3],by decide⟩

def partWalk4 : G.Walk 1 1 :=
  .cons (show G.Adj 1 6 from edge_mem 4 0) <|
  .cons (show G.Adj 6 14 from (show G.Adj 14 6 from edge_mem 4 2).symm) <|
  .cons (show G.Adj 14 1 from (show G.Adj 1 14 from edge_mem 4 1).symm) .nil
lemma partWalk4_cycle : partWalk4.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [partWalk4],by decide⟩

def partWalk : Fin 5 → Σ v, G.Walk v v := ![⟨0,partWalk0⟩, ⟨0,partWalk1⟩, ⟨0,partWalk2⟩, ⟨5,partWalk3⟩, ⟨1,partWalk4⟩]
lemma partWalk_cycle (i : Fin 5) : (partWalk i).2.IsCycle := by
  fin_cases i
  · exact partWalk0_cycle
  · exact partWalk1_cycle
  · exact partWalk2_cycle
  · exact partWalk3_cycle
  · exact partWalk4_cycle
lemma partWalk_disjoint (i j : Fin 5) (hij : i ≠ j) :
    List.Disjoint (partWalk i).2.edges (partWalk j).2.edges := by
  have hh : ∀ i j : Fin 5, i ≠ j →
      Disjoint (partWalk i).2.edges.toFinset (partWalk j).2.edges.toFinset := by decide
  intro e he hf
  exact Finset.disjoint_left.mp (hh i j hij)
    (List.mem_toFinset.mpr he) (List.mem_toFinset.mpr hf)

lemma partWalk_cover (u v : V) :
    G.Adj u v ↔ ∃ i : Fin 5, s(u,v) ∈ (partWalk i).2.edges := by
  constructor
  · intro h
    obtain ⟨⟨e,j⟩,he⟩ := edge_cases u v h
    have hc : ∀ e : E, ∀ j : Fin 3, ∃ i : Fin 5,
        edge e j ∈ (partWalk i).2.edges := by
      intro e j
      fin_cases e <;> fin_cases j <;> decide
    simpa only [he] using hc e j
  · rintro ⟨i,hi⟩
    exact (partWalk i).2.adj_of_mem_edges hi

lemma exists_five_cycle_partition : ∃ D : Finset G.Subgraph,
    (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
    IsDecomposition G D ∧ D.card = 5 := by
  obtain ⟨D,hc,hd,hcard⟩ := upper_of_walk_family G partWalk
    partWalk_cycle partWalk_disjoint partWalk_cover
  have hc' : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2 := by
    simpa only [IsRegularOfDegree,← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using hc
  have hl := cycle_decomposition_card_lower D (fun H hH => ⟨(hc H hH).1,by
    simpa only [IsRegularOfDegree,← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using (hc H hH).2⟩) hd
  refine ⟨D,hc',hd,?_⟩
  simpa only [Fintype.card_fin] using le_antisymm hcard hl

lemma cycleNumber_eq_five : cycleNumber G = 5 := by
  refine cycleNumber_eq G 5 ?_ ?_
  · obtain ⟨D,hc,hd,hcard⟩ := exists_five_cycle_partition
    refine ⟨D,?_,hd,hcard.le⟩
    simpa only [IsRegularOfDegree,← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using hc
  · intro D hc hd
    apply cycle_decomposition_card_lower D ?_ hd
    simpa only [IsRegularOfDegree,← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using hc

end Erdos184.DoubledPetersenSimple
