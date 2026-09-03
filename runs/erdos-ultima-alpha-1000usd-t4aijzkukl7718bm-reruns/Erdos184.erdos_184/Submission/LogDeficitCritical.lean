import Submission.LogDeficitExpansion

/-! Lexicographic criticality for the logarithmic-deficit budget.
This does not exclude the extracted counterexamples. -/
open SimpleGraph
open scoped Classical
namespace Erdos184.LogDeficitSeparator
open ExactVertexSmoothing LogDeficit
universe u
set_option maxHeartbeats 1000000

/-- First minimize order, then minimize edge count, allowing arbitrary new edges. -/
def IsLexMinimal {V : Type u} [Fintype V] (C : ℕ) (G : SimpleGraph V) : Prop :=
  IsVertexMinimal C G ∧
  ∀ {W : Type u} [Fintype W] (H : SimpleGraph W),
    Fintype.card W = Fintype.card V → H.edgeSet.ncard < G.edgeSet.ncard →
    (∀ w, Even (H.degree w)) → HasBound C H

lemma exists_lex_minimal {V : Type u} [Fintype V] (C : ℕ) (G : SimpleGraph V)
    (he : ∀ v, Even (G.degree v)) (hb : ¬HasBound C G) :
    ∃ (W : Type u) (_ : Fintype W) (H : SimpleGraph W), IsLexMinimal C H := by
  obtain ⟨X,instX,A,hA⟩ := exists_vertex_minimal C G he hb
  letI := instX
  let P (m : ℕ) := ∃ (W : Type u) (_ : Fintype W) (H : SimpleGraph W),
    (∀ w, Even (H.degree w)) ∧ ¬HasBound C H ∧
    Fintype.card W = Fintype.card X ∧ H.edgeSet.ncard = m
  have hex : ∃ m, P m := ⟨_,X,instX,A,hA.1,hA.2.1,rfl,rfl⟩
  obtain ⟨W,instW,H,heH,hbH,hn,hm⟩ := Nat.find_spec hex
  letI := instW
  refine ⟨W,instW,H,⟨heH,hbH,?_⟩,?_⟩
  · intro Y instY K hlt heK
    exact hA.2.2 K (by omega) heK
  · intro Y instY K hcard hlt heK
    by_contra hbK
    have hmin := Nat.find_min' hex
      (show P K.edgeSet.ncard from ⟨Y,instY,K,heK,hbK,hcard.trans hn,rfl⟩)
    omega

/-- Every specified cycle has an optimum extension, with the exact shifted value. -/
lemma IsLexMinimal.extend_cycle {V : Type u} [Fintype V] {C : ℕ} {G : SimpleGraph V}
    (hG : IsLexMinimal C G) (H : G.Subgraph)
    (hH : H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) :
    ∃ D : Finset G.Subgraph,
      (∀ K ∈ D, K.coe.Connected ∧ K.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G D ∧ H ∈ D ∧ D.card = budget C (Fintype.card V) + 1 := by
  let P : Finset G.Subgraph := {H}
  have hc : ∀ K ∈ P, K.coe.Connected ∧ K.coe.IsRegularOfDegree 2 := by
    intro K hK
    obtain rfl := Finset.mem_singleton.mp hK
    exact hH
  have hd : Set.PairwiseDisjoint (P : Set G.Subgraph) (fun K => K.edgeSet) := by simp [P]
  have heR := even_residual_of_cycle_packing G hG.1.1 P hc hd
  obtain ⟨F,hcF,hdF,hbF⟩ := hG.2 (G \ unionPieces G P) rfl
    (MinimalCounterexample.residual_edge_card_lt G P (Finset.singleton_nonempty _) hc) (by
      intro w
      simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using heR w)
  obtain ⟨D,hcD,hdD,hPD,hbD⟩ := complete_cycle_packing_extension G P hc hd F (by
    intro K hK
    refine ⟨(hcF K hK).1,?_⟩
    intro w
    simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using (hcF K hK).2 w) hdF
  have hbad : budget C (Fintype.card V) < D.card := by
    by_contra! h
    exact hG.1.2.1 ⟨D,hcD,hdD,h⟩
  have hP : P.card = 1 := Finset.card_singleton _
  exact ⟨D,hcD,hdD,hPD (Finset.mem_singleton_self H),by omega⟩

lemma IsLexMinimal.allCyclesOptimal {V : Type u} [Fintype V] {C : ℕ} {G : SimpleGraph V}
    (hG : IsLexMinimal C G) : MinimalCounterexample.AllCyclesOptimal G := by
  intro H hH
  obtain ⟨D,hD,hd,hHD,hn⟩ := hG.extend_cycle H hH
  refine ⟨D,hD,hd,hHD,?_⟩
  intro E hE he
  have hbad : budget C (Fintype.card V) < E.card := by
    by_contra! h
    exact hG.1.2.1 ⟨E,hE,he,h⟩
  omega


end Erdos184.LogDeficitSeparator
