import Submission.OrderedCutBudget
import Submission.EraseCyclePiece
import Submission.CycleNumberSubmodularity
import Submission.Cuts
import Submission.HamiltonPackingConnectivity

/-! A generic checker for the finite triangle-forcing obstruction.
This is not a settlement of Erdos 184. -/
open SimpleGraph
open scoped Classical
namespace Erdos184.TriangleCertificate
open CycleNumberSubmodularity
variable {U : Type*} [Fintype U]

def Pure (G : SimpleGraph U) (D : Finset G.Subgraph) : Prop :=
  ∀ H ∈ D, H.coe.Connected ∧ ∀ v, Nat.card (H.coe.neighborSet v) = 2

lemma pure_iff (G : SimpleGraph U) (D : Finset G.Subgraph) :
    Pure G D ↔ ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2 := by
  simp only [Pure,IsRegularOfDegree,← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]

lemma even_connected (G : SimpleGraph U)
    (he : ∀ v, Even (Nat.card (G.neighborSet v)))
    (hG : G.IsEdgeConnected 3) : G.IsEdgeConnected 4 := by
  apply HamiltonPackingConnectivity.even_edge_connected_succ G _ 3 (by decide) hG
  intro v
  simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using he v

lemma check (G T : SimpleGraph U) (p : Fin 3 → Σ v, G.Walk v v)
    (hp : ∀ i, (p i).2.IsCycle)
    (hdis : ∀ i j, i ≠ j → List.Disjoint (p i).2.edges (p j).2.edges)
    (hcover : ∀ u v, G.Adj u v ↔ ∃ i, s(u,v) ∈ (p i).2.edges)
    (hdeg : ∀ v, Nat.card (G.neighborSet v) = 6)
    {a : U} (tri : G.Walk a a) (htri : tri.IsCycle)
    (hgraph : tri.toSubgraph.spanningCoe = T) (htc : T.edgeSet.ncard ≤ 3)
    (label : U → Fin 4) (rep : Fin 4 → U) (hr : Function.RightInverse rep label)
    (hs : (∑ j, Nat.card ((G \ T).neighborSet (rep j))) = 22)
    (hv : OrderedCutBudget.variation (G \ T) label = 12) :
    cycleNumber G = 3 ∧ G.IsEdgeConnected 6 ∧ (G \ T).IsEdgeConnected 4 ∧
      (∀ D : Finset (G \ T).Subgraph, Pure (G \ T) D → IsDecomposition (G \ T) D →
        5 ≤ D.card) ∧
      (∀ D : Finset G.Subgraph, Pure G D → IsDecomposition G D →
        tri.toSubgraph ∈ D → 6 ≤ D.card) := by
  subst T
  have hu : ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G D ∧ D.card ≤ 3 := by
    simpa only [Fintype.card_fin] using upper_of_walk_family G p hp hdis hcover
  have hl (D : Finset G.Subgraph)
      (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
      (hd : IsDecomposition G D) : 3 ≤ D.card := by
    have h := cycle_decomposition_degree_lower G D hc hd a
    simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card,hdeg] at h
    omega
  have hres (D : Finset (G \ tri.toSubgraph.spanningCoe).Subgraph)
      (hc : Pure (G \ tri.toSubgraph.spanningCoe) D) (hd : IsDecomposition (G \ tri.toSubgraph.spanningCoe) D) : 5 ≤ D.card := by
    have h := OrderedCutBudget.degree_budget label rep hr D ((pure_iff _ _).mp hc) hd
    simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at h
    rw [hs,hv] at h
    omega
  have hforced (D : Finset G.Subgraph) (hc : Pure G D) (hd : IsDecomposition G D)
      (ht : tri.toSubgraph ∈ D) : 6 ≤ D.card := by
    obtain ⟨E,hcE,hdE,hbE⟩ := erase_cycle_piece D ((pure_iff _ _).mp hc) hd tri.toSubgraph ht
    simp only [IsRegularOfDegree,← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hcE
    have hh := hres E hcE hdE
    omega
  have hconn : G.IsEdgeConnected 6 := by
    obtain ⟨D,hc,hd,hb⟩ := hu
    have hh := hl D hc hd
    have hcard : D.card = 3 := by omega
    have hdeq : ∀ v, G.degree v = 2 * D.card := by
      intro v
      simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card,hdeg,hcard]
    have hspan := cycle_decomposition_saturated_verts G D hc hd hdeq
    have h := HamiltonPackingConnectivity.edge_connected_of_spanning_cycle_packing D hc hd.1 hspan
    simpa only [hcard] using h
  have he : ∀ v, Even (G.degree v) := by
    intro v
    simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card,hdeg]
    decide
  have her : ∀ v, Even (Nat.card ((G \ tri.toSubgraph.spanningCoe).neighborSet v)) := by
    have h := even_delete_cycle he htri
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using h
  have hcr : (G \ tri.toSubgraph.spanningCoe).IsEdgeConnected 4 := by
    have h := HamiltonPackingConnectivity.deletion_edge_connected G 3 3 hconn tri.toSubgraph.spanningCoe.edgeSet htc
    simp only [SimpleGraph.deleteEdges,fromEdgeSet_edgeSet] at h
    exact even_connected _ her h
  exact ⟨cycleNumber_eq G 3 hu hl,hconn,hcr,hres,hforced⟩

end Erdos184.TriangleCertificate
