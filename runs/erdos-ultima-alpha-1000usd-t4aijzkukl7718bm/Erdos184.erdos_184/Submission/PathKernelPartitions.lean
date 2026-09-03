import Submission.PathKernelTransport

/-! Exact correspondence of graph and kernel partition cardinalities,
including maximum as well as minimum counts. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.GraphCircuitCode
open Erdos184Serial
set_option maxHeartbeats 1500000
variable {V : Type*} [Fintype V] {G R : SimpleGraph V}

lemma decomposition_of_partition {P : Finset (Finset (Sym2 V))}
    (hP : Partition (code G) R.edgeFinset P) :
    ∃ D : Finset R.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition R D ∧ D.card = P.card := by
  obtain ⟨A,hA,hdis,hcover,hcard⟩ := circuit_partition_graph hP
  have he : (⋃ H ∈ A, H.edgeSet) = R.edgeSet := by
    rw [hcover]
    ext e
    exact SimpleGraph.mem_edgeFinset
  refine ⟨Subfamilies.lowerFamily A he,?_,Subfamilies.lowerFamily_decomposition A he hdis,?_⟩
  · simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using Subfamilies.lowerFamily_property
        (fun {_} [_] H => H.Connected ∧ H.IsRegularOfDegree 2) A he (by
          simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
            ← Nat.card_eq_fintype_card] using hA)
  · rw [Subfamilies.lowerFamily_card,hcard]
end Erdos184Work.GraphCircuitCode

namespace Erdos184Work.PathSubstitution.Family
open Erdos184Serial
set_option maxHeartbeats 1800000
variable {V W J : Type*} [Fintype V] [Fintype J] {G : SimpleGraph V} (F : Family J W G)
    (hcover : ∀ x y, G.Adj x y → ∃ j, s(x,y) ∈ (F.path j).edges)
include hcover

lemma decomposition_of_kernel_partition {s : Finset J} {P : Finset (Finset J)}
    (hP : Partition (LabelKernel.code F.src F.dst) s P) :
    ∃ D : Finset (F.expandGraph s).Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition (F.expandGraph s) D ∧ D.card = P.card := by
  have hQ := (F.supportTransport hcover).map_partition hP
  change Partition (GraphCircuitCode.code G) (F.expandEdges s)
    (P.image F.expandEdges) at hQ
  rw [← F.expandGraph_edgeFinset] at hQ
  obtain ⟨D,hD,hdD,hcD⟩ := GraphCircuitCode.decomposition_of_partition hQ
  exact ⟨D,hD,hdD,hcD.trans ((F.supportTransport hcover).map_card P)⟩

lemma kernel_partition_of_decomposition {s : Finset J}
    (D : Finset (F.expandGraph s).Subgraph)
    (hD : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition (F.expandGraph s) D) :
    ∃ P, Partition (LabelKernel.code F.src F.dst) s P ∧ P.card = D.card := by
  obtain ⟨hP,hcard⟩ := GraphCircuitCode.graph_cycle_partition (F.expandGraph_le s) D hD hd
  rw [F.expandGraph_edgeFinset] at hP
  obtain ⟨P,hP',hcP⟩ := (F.supportTransport hcover).unmap_partition hP
  exact ⟨P,hP',hcP.trans hcard⟩

lemma kernel_upper_bound_iff (s : Finset J) (k : ℕ) :
    (∀ D : Finset (F.expandGraph s).Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) →
      IsDecomposition (F.expandGraph s) D → D.card ≤ k) ↔
    (∀ P, Partition (LabelKernel.code F.src F.dst) s P → P.card ≤ k) := by
  constructor
  · intro hb P hP
    obtain ⟨D,hD,hdD,hcard⟩ := F.decomposition_of_kernel_partition hcover hP
    rw [← hcard]
    exact hb D hD hdD
  · intro hb D hD hdD
    obtain ⟨P,hP,hcard⟩ := F.kernel_partition_of_decomposition hcover D hD hdD
    rw [← hcard]
    exact hb P hP

#print axioms decomposition_of_kernel_partition
#print axioms kernel_upper_bound_iff
end Erdos184Work.PathSubstitution.Family
