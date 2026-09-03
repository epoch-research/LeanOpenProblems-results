import Submission.ShiftFiveCritical

/-!
Separator budgets for fifth-intercept critical graphs. The existence of a
packing violating these necessary conditions is not asserted.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184.ShiftFiveCritical
open ExactVertexSmoothing
universe u
set_option maxHeartbeats 800000

/-- A separator of size s saves C(5-s), and four-terminal gluing costs four.
For s at most three, the gluing overhead is zero. -/
lemma IsVertexMinimal.packing_no_small_split {V : Type u} [Fintype V]
    {C : ℕ} {G : SimpleGraph V} (hG : IsVertexMinimal C G)
    (P : Finset G.Subgraph)
    (hcP : ∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hdP : Set.PairwiseDisjoint (P : Set G.Subgraph) (fun H => H.edgeSet))
    (S : Set V) (hS : S.ncard ≤ 4)
    (hp : P.card + (if S.ncard ≤ 3 then 0 else 4) ≤ C * (5-S.ncard))
    (A B : SimpleGraph V)
    (hA : A ≤ G \ unionPieces G P) (hB : B ≤ G \ unionPieces G P)
    (hdis : Disjoint A.edgeSet B.edgeSet)
    (hcover : A.edgeSet ∪ B.edgeSet = (G \ unionPieces G P).edgeSet)
    (hinter : A.support ∩ B.support ⊆ S)
    (hAc : 6 ≤ A.support.ncard) (hBc : 6 ≤ B.support.ncard)
    (hAl : A.support.ncard < Fintype.card V) (hBl : B.support.ncard < Fintype.card V) : False := by
  obtain ⟨D,hcD,hdD,hbD⟩ := FiniteTerminalGluing.decomposition_of_small_separation
    (G := G \ unionPieces G P) S hS
    (by
      intro x
      simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
        using even_residual_of_cycle_packing G hG.1 P hcP hdP x)
    hA hB hdis hcover hinter (C * charge A.support.ncard) (C * charge B.support.ncard)
    (fun X hs he => hG.bound_on_support_subset X A.support hs hAl he)
    (fun Y hs he => hG.bound_on_support_subset Y B.support hs hBl he)
  obtain ⟨E,hcE,hdE,hbE⟩ := complete_cycle_packing G P hcP hdP D (by
    intro H hH
    refine ⟨(hcD H hH).1,?_⟩
    intro x
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using (hcD H hH).2 x) hdD
  have hover := Set.ncard_le_ncard hinter
  have hsum := Set.ncard_union_add_ncard_inter A.support B.support
  rw [support_union_of_edge_cover hcover] at hsum
  have hs : (G \ unionPieces G P).support.ncard ≤ Fintype.card V := by
    simpa using Set.ncard_le_ncard (Set.subset_univ (G \ unionPieces G P).support)
  have hcharge : charge A.support.ncard + charge B.support.ncard + (5-S.ncard) ≤
      charge (Fintype.card V) := by
    unfold charge
    omega
  have hbudget := Nat.mul_le_mul_left C hcharge
  simp only [Nat.mul_add] at hbudget
  exact hG.2.1 ⟨E,hcE,hdE,by omega⟩

/-- Only the chosen endpoints need enough residual degree. Other vertices
may become isolated after the packing is removed. -/
lemma IsVertexMinimal.packing_endpoints_reachable {V : Type u} [Fintype V]
    {C : ℕ} {G : SimpleGraph V} (hG : IsVertexMinimal C G)
    (P : Finset G.Subgraph)
    (hc : ∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (P : Set G.Subgraph) (fun H => H.edgeSet))
    (S : Set V) (hS : S.ncard ≤ 4)
    (hp : P.card + (if S.ncard ≤ 3 then 0 else 4) ≤ C * (5-S.ncard))
    (u w : ↥(Sᶜ))
    (hu : 2*P.card+6 ≤ G.degree u.val) (hw : 2*P.card+6 ≤ G.degree w.val) :
    ((G \ unionPieces G P).induce Sᶜ).Reachable u w := by
  have hdeg (v : V) (hv : 2*P.card+6 ≤ G.degree v) :
      6 ≤ (G \ unionPieces G P).degree v := by
    have hPv := ShiftedCritical.packing_degree_le P hc hd v
    have hr := degree_sdiff_of_le (unionPieces_le G P) v
    simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hv hPv hr ⊢
    omega
  apply FiniteTerminalGluing.induce_compl_reachable_of_endpoint_degrees _ S 6 u w
  · simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hdeg u.val hu
  · simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hdeg w.val hw
  · intro A B hA hB hdis hcover hinter hAc hBc hAl hBl
    exact hG.packing_no_small_split P hc hd S hS hp A B hA hB hdis hcover hinter hAc hBc hAl hBl

/-- Removing at most C-4 cycles preserves five-vertex connectivity. -/
lemma IsVertexMinimal.small_packing_induce_compl_reachable {V : Type u} [Fintype V]
    {C : ℕ} {G : SimpleGraph V} (hG : IsVertexMinimal C G) (hC : 15 ≤ C)
    (P : Finset G.Subgraph)
    (hc : ∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (P : Set G.Subgraph) (fun H => H.edgeSet))
    (hp : P.card+4 ≤ C) (S : Set V) (hS : S.ncard ≤ 4) (u w : ↥(Sᶜ)) :
    ((G \ unionPieces G P).induce Sᶜ).Reachable u w := by
  apply hG.packing_endpoints_reachable P hc hd S hS
  · have hone : 1 ≤ 5-S.ncard := by omega
    have hmul := Nat.mul_le_mul_left C hone
    by_cases hh : S.ncard ≤ 3 <;> simp only [hh,if_true,if_false,Nat.add_zero] <;> omega
  · have hh := hG.degree_lower hC u.val
    omega
  · have hh := hG.degree_lower hC w.val
    omega

end Erdos184.ShiftFiveCritical
