import Submission.JunctionLayout

/-! Exact counts for every color subfamily of an assembled contact kernel. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.PathSubstitution.Family
open Erdos184Serial MaximumCycles
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
variable {V W K : Type*} [Fintype V] [Fintype K] {G : SimpleGraph V}
    {m : K → ℕ} (F : Family (Σ i, Fin (m i)) W G)
    (root : K → V) (C : ∀ i, G.Walk (root i) (root i))
    (hC : ∀ i, (C i).IsCycle)
    (hd : ∀ i j, i ≠ j → (C i).edges.Disjoint (C j).edges)
    (hpiece : ∀ i e, e ∈ (C i).edges ↔ ∃ j, e ∈ (F.path ⟨i,j⟩).edges)

noncomputable local instance : DecidableEq (Σ i, Fin (m i)) := Classical.decEq _

include hC hd hpiece in
lemma colorLabels_valid (A : Finset K) : F.validLabels (colorLabels A) := by
  apply (F.expandGraph_even_iff _).mp
  have hreg : ∀ H ∈ A.image (fun i => (C i).toSubgraph),
      H.coe.Connected ∧ H.coe.IsRegularOfDegree 2 := by
    intro H hH
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hH
    exact cycle_coe_regular G (hC i)
  have hdis : Set.PairwiseDisjoint (↑(A.image (fun i => (C i).toSubgraph)) : Set G.Subgraph)
      (fun H => H.edgeSet) := by
    intro H hH L hL hHL
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hH
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hL
    apply Set.disjoint_left.mpr
    intro e he hf
    exact List.disjoint_left.mp (hd i j (fun h => hHL (by subst j; rfl)))
      ((C i).mem_edges_toSubgraph.mp he) ((C j).mem_edges_toSubgraph.mp hf)
  have he := cycle_subfamily_even _ hreg hdis
  simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at he ⊢
  rw [F.expandGraph_colorLabels root C hpiece A]
  exact he

include hC hd hpiece in
lemma color_number_iff
    (hcover : ∀ x y, G.Adj x y → ∃ j, s(x,y) ∈ (F.path j).edges)
    (A : Finset K) (k : ℕ) :
    Critical.number (subfamilyGraph (A.image (fun i => (C i).toSubgraph))) = k ↔
      HasNumber (LabelKernel.code F.src F.dst) (colorLabels A) k := by
  have hh := F.number_expandGraph_iff hcover (colorLabels A)
    (F.colorLabels_valid root C hC hd hpiece A) k
  rwa [F.expandGraph_colorLabels root C hpiece A] at hh

include hpiece in
lemma color_maximum_bound_iff
    (hcover : ∀ x y, G.Adj x y → ∃ j, s(x,y) ∈ (F.path j).edges)
    (A : Finset K) (k : ℕ) :
    (∀ D : Finset (subfamilyGraph (A.image (fun i => (C i).toSubgraph))).Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) →
      IsDecomposition _ D → D.card ≤ k) ↔
    (∀ P, Partition (LabelKernel.code F.src F.dst) (colorLabels A) P → P.card ≤ k) := by
  have hh := F.kernel_upper_bound_iff hcover (colorLabels A) k
  rw [F.expandGraph_colorLabels root C hpiece A] at hh
  exact hh

#print axioms color_number_iff
#print axioms color_maximum_bound_iff
end Erdos184Work.PathSubstitution.Family
