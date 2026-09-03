import Submission.TransferSingletonForest
import Submission.ChainRingPieces
import Submission.ParityDegreeLower

/-! Finite data for a Best-edge transfer with strict RAW-number loss.
No hull loss or disproof of Erdős184 is asserted. -/
open SimpleGraph
namespace Erdos184Work.BestTransferRaw
open Critical CycleForestCertificate
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
abbrev V := Fin 13
def leftEdges : List (V × V) := [(0,1),(0,2),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(2,4),(2,5),(2,6)]
def rightEdges : List (V × V) := [(3,7),(3,8),(3,10),(3,11),(3,12),(7,8),(7,9),(7,10),(7,11),(7,12),(8,9),(8,10),(8,11),(8,12)]
def block (i : Fin 2) : SimpleGraph V := SimpleGraph.fromRel (fun x y =>
  (x,y) ∈ if i = 0 then leftEdges else rightEdges)
instance (i : Fin 2) : DecidableRel (block i).Adj := by unfold block; infer_instance
def base : SimpleGraph V := block 0 ⊔ block 1
instance : DecidableRel base.Adj := by unfold base; infer_instance
def closing : SimpleGraph V := SimpleGraph.fromRel (fun x y => x = 0 ∧ y = 9)
instance : DecidableRel closing.Adj := by unfold closing; infer_instance
def source : SimpleGraph V := base ⊔ closing
instance : DecidableRel source.Adj := by unfold source; infer_instance
def forest : SimpleGraph V := SimpleGraph.fromRel (fun x y =>
  (x,y) ∈ ([(0,4),(0,5),(0,6),(0,9),(3,10),(3,11),(3,12)] : List (V × V)))
instance : DecidableRel forest.Adj := by unfold forest; infer_instance
def target : SimpleGraph V := SimpleGraph.fromRel (fun x y =>
  (x,y) ∈ ([(0,1),(0,2),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(2,4),(2,5),(2,6),(3,7),(3,8),(3,10),(3,11),(3,12),(7,8),(7,10),(7,11),(7,12),(8,10),(8,11),(8,12),(0,9),(0,7),(0,8)] : List (V × V)))
instance : DecidableRel target.Adj := by unfold target; infer_instance
def evenSource : SimpleGraph V := source \ forest
instance : DecidableRel evenSource.Adj := by unfold evenSource; infer_instance
def evenTarget : SimpleGraph V := target \ forest
instance : DecidableRel evenTarget.Adj := by unfold evenTarget; infer_instance

def leftPort : Fin 2 → V := ![0,3]
def rightPort : Fin 2 → V := ![3,9]
def hubOne : Fin 2 → V := ![1,7]
def hubTwo : Fin 2 → V := ![2,8]
def hubs (i : Fin 2) : Finset V := {leftPort i,hubOne i,hubTwo i}
def rights (i : Fin 2) : Finset V := if i = 0 then {3,4,5,6} else {9,10,11,12}
def interiorRights (i : Fin 2) : Finset V := (rights i).erase (rightPort i)
def oddVertices : Finset V := {4,5,6,9,10,11,12}

lemma block_le_source : ∀ i, block i ≤ source := by
  change ∀ i x y, (block i).Adj x y → source.Adj x y
  decide +kernel
lemma block_no_closing : ∀ i x y, ¬ ((block i).Adj x y ∧ closing.Adj x y) := by decide +kernel
lemma blocks_disjoint : ∀ i j, i ≠ j → ∀ x y, ¬ ((block i).Adj x y ∧ (block j).Adj x y) := by decide +kernel
lemma source_edge_cases : ∀ x y, source.Adj x y → closing.Adj x y ∨ ∃ i, (block i).Adj x y := by decide +kernel
lemma closing_adj_iff : ∀ x y, closing.Adj x y ↔ (x = 0 ∧ y = 9) ∨ (x = 9 ∧ y = 0) := by decide +kernel
lemma source_closing : source.Adj 0 9 := by decide +kernel
lemma base_no_closing : ¬ base.Adj 0 9 := by decide +kernel
lemma ports_ne : ∀ i, leftPort i ≠ rightPort i := by decide +kernel
lemma block_internal_or_zero : ∀ i v, v ≠ leftPort i → v ≠ rightPort i →
    (∀ w, (block i).Adj v w ↔ source.Adj v w) ∨ (∀ w, ¬ (block i).Adj v w) := by decide +kernel
lemma closing_degree_left : closing.degree 0 = 1 := by decide +kernel
lemma closing_degree_right : closing.degree 9 = 1 := by decide +kernel
lemma block_degrees : ∀ i, (block i).degree (leftPort i) = 5 ∧
    (block i).degree (hubOne i) = 6 ∧ (block i).degree (hubTwo i) = 6 ∧
    (block i).degree (rightPort i) = 2 := by decide +kernel
lemma interior_degree : ∀ i v, v ∈ interiorRights i → (block i).degree v = 3 := by decide +kernel
lemma rights_cover : ∀ i v, v ∈ rights i → v = rightPort i ∨ v ∈ interiorRights i := by decide +kernel
lemma interior_not_ports : ∀ i v, v ∈ interiorRights i → v ≠ leftPort i ∧ v ≠ rightPort i := by decide +kernel
lemma rights_independent : ∀ i u, u ∈ rights i → ∀ v, v ∈ rights i → ¬ source.Adj u v := by decide +kernel
lemma sizes : ∀ i, (hubs i).card = 3 ∧ (rights i).card = 4 ∧ (interiorRights i).card = 3 := by decide +kernel
lemma hubs_rights_disjoint : ∀ i, Disjoint (hubs i) (rights i) := by decide +kernel
lemma interior_subset : ∀ i, interiorRights i ⊆ rights i := by decide +kernel
lemma hubs_interior_disjoint : ∀ i, Disjoint (hubs i) (interiorRights i) := by decide +kernel
lemma odd_vertices : ∀ v ∈ oddVertices, Odd (source.degree v) := by decide +kernel
lemma odd_independent : ∀ u ∈ oddVertices, ∀ v ∈ oddVertices, ¬ source.Adj u v := by decide +kernel
lemma odd_card : oddVertices.card = 7 := by decide +kernel
lemma forest_le_source : forest ≤ source := by
  change ∀ u v, forest.Adj u v → source.Adj u v
  decide +kernel
lemma forest_le_target : forest ≤ target := by
  change ∀ u v, forest.Adj u v → target.Adj u v
  decide +kernel
lemma forest_card : Nat.card forest.edgeSet = 7 := by
  have h : forest.edgeFinset.card = 7 := by decide +kernel
  simpa only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] using h
lemma source_even : ∀ v, Even (Nat.card (evenSource.neighborSet v)) := by
  have h : ∀ v, Even (evenSource.degree v) := by decide +kernel
  simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using h
lemma forest_pair : forest.Adj 0 9 := by decide +kernel
lemma transfer_eq : Compression.transfer source 0 9 = target := by
  ext x y
  simp only [Compression.transfer, SimpleGraph.sup_adj, SimpleGraph.sdiff_adj, SimpleGraph.fromRel_adj]
  revert x y
  decide +kernel

end Erdos184Work.BestTransferRaw
#print axioms Erdos184Work.BestTransferRaw.transfer_eq
