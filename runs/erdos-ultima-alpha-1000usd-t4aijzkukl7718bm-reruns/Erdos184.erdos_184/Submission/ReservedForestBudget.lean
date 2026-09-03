import Submission.CycleMixing

/-!
An edge-budget obstruction to bounded-forest absorption of a reserved critical
cycle family.  This is not a proof or disproof of Erdős 184.
-/
open SimpleGraph
open scoped Classical BigOperators
namespace Erdos184.ReservedForestBudget
variable {V : Type*} [Fintype V]

lemma unmarked_edges_lower (G R : SimpleGraph V) (hRG : R ≤ G)
    (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D)
    (hR : R.edgeFinset.card + 1 ≤ D.card) :
    2 * D.card + 1 ≤ (G \ R).edgeFinset.card := by
  have hthree := cycle_decomposition_three_mul_card_le_edges G D hc hd
  have hsub : R.edgeFinset ⊆ G.edgeFinset := by
    intro e he
    exact mem_edgeFinset.mpr (edgeSet_mono hRG (mem_edgeFinset.mp he))
  have heq : (G \ R).edgeFinset = G.edgeFinset \ R.edgeFinset := by
    ext e
    simp only [mem_edgeFinset, Finset.mem_sdiff, edgeSet_sdiff, Set.mem_diff]
  have hsum := Finset.card_sdiff_add_card_eq_card hsub
  rw [← heq] at hsum
  omega

lemma forest_cover_edge_bound [Nonempty V] {I : Type*} [Fintype I]
    (B : SimpleGraph V) (F : I → SimpleGraph V)
    (hf : ∀ i, (F i).IsAcyclic) (hcover : B ≤ ⨆ i, F i) :
    B.edgeFinset.card ≤ Fintype.card I * (Fintype.card V - 1) := by
  have hsub : B.edgeFinset ⊆ Finset.univ.biUnion (fun i : I => (F i).edgeFinset) := by
    intro e he
    have h := edgeSet_mono hcover (mem_edgeFinset.mp he)
    induction e using Sym2.ind with
    | h u v =>
      have hh : ∃ i, (F i).Adj u v := by simpa only [mem_edgeSet, iSup_adj] using h
      obtain ⟨i,hi⟩ := hh
      exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ i,mem_edgeFinset.mpr hi⟩
  calc
    B.edgeFinset.card ≤ (Finset.univ.biUnion (fun i : I => (F i).edgeFinset)).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ i : I, (F i).edgeFinset.card := Finset.card_biUnion_le
    _ ≤ ∑ _i : I, (Fintype.card V - 1) := by
      apply Finset.sum_le_sum
      intro i _
      have h := forest_edge_card_lt_vertex_card (F i) (hf i)
      omega
    _ = Fintype.card I * (Fintype.card V - 1) := by simp

/-- Even a cover by 2*C forests is impossible for the unmarked complement
when the partition has C*(n-1)+1 cycles and at most C*(n-1) edges are marked.
Neither criticality nor tree structure of the marked graph is needed here. -/
lemma no_two_mul_forest_cover [Nonempty V] (C : ℕ)
    (G R : SimpleGraph V) (hRG : R ≤ G) (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D)
    (hD : D.card = C * (Fintype.card V - 1) + 1)
    (hR : R.edgeFinset.card ≤ C * (Fintype.card V - 1))
    (F : Fin (2*C) → SimpleGraph V) (hf : ∀ i, (F i).IsAcyclic) :
    ¬ G \ R ≤ ⨆ i, F i := by
  intro hcover
  have hlo := unmarked_edges_lower G R hRG D hc hd (by omega)
  have hup := forest_cover_edge_bound (G \ R) F hf hcover
  rw [hD] at hlo
  simp only [Fintype.card_fin] at hup
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card,
    Nat.card_coe_set_eq] at hlo hup
  rw [mul_assoc] at hup
  omega

end Erdos184.ReservedForestBudget
