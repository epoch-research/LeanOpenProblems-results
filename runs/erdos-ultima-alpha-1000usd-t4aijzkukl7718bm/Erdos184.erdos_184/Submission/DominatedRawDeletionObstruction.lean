import Submission.DominatedSingletonRemainder
import Submission.PerfectForestHull

/-! A six-vertex obstruction to replacing the deleted graph's hull by its raw
number in a loss-two assertion at a dominated best-singleton leaf. The source
is not asserted to be globally minimal. This is not an Erdos184 disproof. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.DominatedRawDeletionObstruction
open Critical SingletonExchange
set_option maxHeartbeats 800000
abbrev V := Fin 6

def graph : SimpleGraph V := SimpleGraph.fromRel (fun x y =>
  (x,y) ∈ ([(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(1,4),(1,5),(2,5),(3,4)] : List (V × V)))
instance : DecidableRel graph.Adj := by unfold graph; infer_instance

def forest : SimpleGraph V := SimpleGraph.fromRel (fun x y =>
  (x,y) ∈ ([(0,1),(2,5),(3,4)] : List (V × V)))
instance : DecidableRel forest.Adj := by unfold forest; infer_instance

def remainder : SimpleGraph V := graph \ forest
instance : DecidableRel remainder.Adj := by unfold remainder; infer_instance

def deleted : SimpleGraph V := graph.deleteIncidenceSet 0
instance : DecidableRel deleted.Adj := by unfold deleted; infer_instance

lemma forest_le : forest ≤ graph := by
  change ∀ u v, forest.Adj u v → graph.Adj u v
  decide +kernel
lemma forest_card : Nat.card forest.edgeSet = 3 := by
  have h : forest.edgeFinset.card = 3 := by decide +kernel
  simpa only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] using h
lemma graph_odd : ∀ v : V, Odd (Nat.card (graph.neighborSet v)) := by
  have h : ∀ v : V, Odd (graph.degree v) := by decide +kernel
  simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using h
lemma remainder_even : ∀ v : V, Even (Nat.card (remainder.neighborSet v)) := by
  have h : ∀ v : V, Even (remainder.degree v) := by decide +kernel
  simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using h

def c0 : remainder.Walk 0 0 :=
  .cons (show remainder.Adj 0 2 by decide +kernel)
    (.cons (show remainder.Adj 2 1 by decide +kernel)
    (.cons (show remainder.Adj 1 3 by decide +kernel)
    (.cons (show remainder.Adj 3 0 by decide +kernel) .nil)))
def c1 : remainder.Walk 0 0 :=
  .cons (show remainder.Adj 0 4 by decide +kernel)
    (.cons (show remainder.Adj 4 1 by decide +kernel)
    (.cons (show remainder.Adj 1 5 by decide +kernel)
    (.cons (show remainder.Adj 5 0 by decide +kernel) .nil)))
lemma c0_cycle : c0.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide +kernel
lemma c1_cycle : c1.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide +kernel

lemma remainder_number : number remainder = 2 := by
  have hu : number remainder ≤ 2 := by
    apply LocalObstruction.number_le_two_cycles c0 c1 c0_cycle c1_cycle
    · apply List.disjoint_toFinset_iff_disjoint.mp
      decide +kernel
    · decide +kernel
  have hl := StarCore.number_degree_bound remainder 0
  have hd : remainder.degree 0 = 4 := by decide +kernel
  simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hl hd
  omega

lemma graph_number : number graph = 5 := by
  have hu := SingletonExchange.split_lower_bound forest_le
  change number graph ≤ number remainder + Nat.card forest.edgeSet at hu
  rw [remainder_number,forest_card] at hu
  obtain ⟨D,hD,hdec,hcard⟩ := exists_minimum graph
  have hs := MinimumParity.all_odd_singleton_bound graph_odd D hD hdec
  have hs' : 3 ≤ (edgePieces D).card := by
    norm_num at hs
    omega
  have hd := ParityDegreeLower.degree_parity_bound D hD hdec
    ({0,1} : Finset V) ({2,3,4,5} : Finset V) (by decide +kernel)
    (by decide +kernel) (fun v _ => by
      simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
        using graph_odd v) 3 hs'
  have hsum : (∑ v ∈ ({0,1} : Finset V), graph.degree v) = 10 := by decide +kernel
  have hA : ({0,1} : Finset V).card = 2 := by decide +kernel
  have hO : ({2,3,4,5} : Finset V).card = 4 := by decide +kernel
  simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hd hsum
  rw [hsum,hA,hO,hcard] at hd
  omega

lemma forest_best : Best graph forest := by
  refine ⟨⟨forest_le,remainder_even,?_⟩,?_⟩
  · change number remainder + Nat.card forest.edgeSet = number graph
    rw [remainder_number,forest_card,graph_number]
  · intro T hT
    rw [forest_card]
    have hd (v : V) : 1 ≤ T.degree v := by
      have h := degree_sdiff_add graph T hT.1 v
      have he := Nat.even_iff.mp (hT.2.1 v)
      have ho := Nat.odd_iff.mp (graph_odd v)
      simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at h ⊢
      omega
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun v _ => hd v)
    rw [T.sum_degrees_eq_twice_card_edges] at hs
    have hconst : (∑ _v : V, (1 : ℕ)) = 6 := by decide +kernel
    rw [hconst] at hs
    have he : T.edgeFinset.card = Nat.card T.edgeSet := by
      rw [SimpleGraph.edgeFinset_card,Nat.card_eq_fintype_card]
    rw [he] at hs
    omega

def d0 : deleted.Walk 1 1 :=
  .cons (show deleted.Adj 1 2 by decide +kernel)
    (.cons (show deleted.Adj 2 5 by decide +kernel)
    (.cons (show deleted.Adj 5 1 by decide +kernel) .nil))
def d1 : deleted.Walk 1 1 :=
  .cons (show deleted.Adj 1 3 by decide +kernel)
    (.cons (show deleted.Adj 3 4 by decide +kernel)
    (.cons (show deleted.Adj 4 1 by decide +kernel) .nil))
lemma d0_cycle : d0.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide +kernel
lemma d1_cycle : d1.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide +kernel

lemma deleted_number : number deleted = 2 := by
  have hu : number deleted ≤ 2 := by
    apply LocalObstruction.number_le_two_cycles d0 d1 d0_cycle d1_cycle
    · apply List.disjoint_toFinset_iff_disjoint.mp
      decide +kernel
    · decide +kernel
  have hl := StarCore.number_degree_bound deleted 1
  have hd : deleted.degree 1 = 4 := by decide +kernel
  simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hl hd
  omega

/-- Only the RAW number version with additive loss two is refuted. -/
lemma dominated_best_leaf_raw_loss :
    Best graph forest ∧ forest.Adj 1 0 ∧
    (∀ w : V, w ≠ 1 → graph.Adj 0 w → graph.Adj 1 w) ∧
    Nat.card (forest.neighborSet 0) = 1 ∧
    number (graph.deleteIncidenceSet 0) + 2 < number graph := by
  refine ⟨forest_best,by decide +kernel,by decide +kernel,?_,?_⟩
  · have h : forest.degree 0 = 1 := by decide +kernel
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using h
  · change number deleted + 2 < number graph
    rw [deleted_number,graph_number]
    omega

end Erdos184Work.DominatedRawDeletionObstruction
#print axioms Erdos184Work.DominatedRawDeletionObstruction.dominated_best_leaf_raw_loss
