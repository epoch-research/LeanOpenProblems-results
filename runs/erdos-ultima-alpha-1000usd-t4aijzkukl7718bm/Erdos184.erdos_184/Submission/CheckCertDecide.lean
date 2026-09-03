import Submission.HullForestReduction
import Submission.VertexSeparatorReduction
import Submission.GraphCircuitCode

/-! Kernel-checkable certificates bounding a decomposition by a contained forest.
These certificates are for specified finite graphs, not a general bound. -/
open SimpleGraph
namespace Erdos184Work.CycleForestCertificate
open Critical
set_option maxHeartbeats 800000
attribute [local instance 2000] Finset.decidableDforallFinset
variable {V : Type*} [Fintype V] [DecidableEq V]

def graph (s : Finset (Sym2 V)) : SimpleGraph V := SimpleGraph.fromEdgeSet (s : Set (Sym2 V))
instance (s : Finset (Sym2 V)) : DecidableRel (graph s).Adj := by
  unfold graph
  infer_instance

def vertices (s : Finset (Sym2 V)) : Finset V := s.biUnion Sym2.toFinset

def PieceValid (s : Finset (Sym2 V)) : Prop :=
  s.card = 1 ∨ ((graph s).induce (vertices s : Set V)).Connected ∧
    ∀ v : (vertices s : Set V), ((graph s).induce (vertices s : Set V)).degree v = 2
instance (s : Finset (Sym2 V)) : Decidable (PieceValid s) := by
  unfold PieceValid
  infer_instance

def ForestValid (s : Finset (Sym2 V)) (r : V → ℕ) : Prop :=
  (∀ u v, (graph s).Adj u v → r u ≠ r v) ∧
  ∀ v u w, (graph s).Adj v u → (graph s).Adj v w →
    r u < r v → r w < r v → u = w
instance (s : Finset (Sym2 V)) (r : V → ℕ) : Decidable (ForestValid s r) := by
  unfold ForestValid
  infer_instance

structure Data (V : Type*) [DecidableEq V] where
  pieces : Finset (Finset (Sym2 V))
  forest : Finset (Sym2 V)
  rank : V → ℕ

def Data.Valid (d : Data V) (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  (∀ s ∈ d.pieces, PieceValid s) ∧
  (∀ s ∈ d.pieces, ∀ t ∈ d.pieces, s ≠ t → Disjoint s t) ∧
  d.pieces.biUnion id = G.edgeFinset ∧
  d.forest ⊆ G.edgeFinset ∧ d.pieces.card ≤ d.forest.card ∧ ForestValid d.forest d.rank

variable (d : Data V) (G : SimpleGraph V) [DecidableRel G.Adj]
#synth Decidable (∀ s ∈ d.pieces, PieceValid s)
#synth Decidable (∀ s ∈ d.pieces, ∀ t ∈ d.pieces, s ≠ t → Disjoint s t)
#synth Decidable (d.pieces.biUnion id = G.edgeFinset)
#synth Decidable (d.forest ⊆ G.edgeFinset)
#synth Decidable (d.pieces.card ≤ d.forest.card)
#synth Decidable (ForestValid d.forest d.rank)
set_option pp.all true in
#print Data.Valid
end Erdos184Work.CycleForestCertificate
