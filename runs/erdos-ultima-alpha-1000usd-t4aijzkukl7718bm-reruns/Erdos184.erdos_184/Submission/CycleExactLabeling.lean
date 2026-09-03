import Submission.CycleVertexLabeling

/-! Exact adjacency labels for an induced cycle piece. -/
open SimpleGraph
open scoped Classical
namespace Erdos184.CycleExactLabeling
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 1000000

lemma eq_of_le_degree_eq (A B : SimpleGraph V) (hAB : A ≤ B)
    (hd : ∀ v, A.degree v = B.degree v) : A = B := by
  ext u v
  have hs : A.neighborFinset u ⊆ B.neighborFinset u := by
    intro w hw
    exact (mem_neighborFinset B u w).mpr (hAB ((mem_neighborFinset A u w).mp hw))
  have heq := Finset.eq_of_subset_of_card_le hs (by
    simpa only [card_neighborFinset_eq_degree] using (hd u).ge)
  rw [← mem_neighborFinset A u v,← mem_neighborFinset B u v,heq]

lemma exists_exact_labels {G : SimpleGraph V} (C : G.Subgraph)
    (hc : C.coe.Connected ∧ C.coe.IsRegularOfDegree 2) (hind : C.IsInduced)
    {n : ℕ} (hlen : C.verts.ncard = n+3) :
    ∃ e : Fin (n+3) ≃ C.verts, ∀ u v,
      G.Adj (e u).val (e v).val ↔ (cycleGraph (n+3)).Adj u v := by
  obtain ⟨f,hf,ha⟩ := CycleVertexLabeling.exists_labels C hc hlen
  let e : Fin (n+3) ≃ C.verts :=
    (Equiv.ofInjective f f.injective).trans (Equiv.setCongr hf)
  have hev (u : Fin (n+3)) : (e u).val = f u := rfl
  let K := C.coe.comap e
  have hreg : K.IsRegularOfDegree 2 := by
    have hh := regular_two_of_iso (Iso.comap e C.coe).symm (by
      intro v
      simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hc.2 v)
    intro v
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hh v
  have hle : cycleGraph (n+3) ≤ K := by
    intro u v huv
    change C.Adj (e u).val (e v).val
    apply hind (e u).property (e v).property
    rw [hev,hev]
    rcases (cycleGraph_adj_successor u v).mp huv with huv | huv
    · rw [huv]
      exact ha u
    · rw [huv]
      exact (ha v).symm
  have heq : cycleGraph (n+3) = K := eq_of_le_degree_eq _ _ hle (by
    intro v
    have hh := hreg v
    simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hh ⊢
    have hd := cycleGraph_degree_three_le (n := n) (v := v)
    simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hd
    omega)
  refine ⟨e,?_⟩
  intro u v
  rw [heq]
  exact ⟨hind (e u).property (e v).property,C.adj_sub⟩

end Erdos184.CycleExactLabeling
