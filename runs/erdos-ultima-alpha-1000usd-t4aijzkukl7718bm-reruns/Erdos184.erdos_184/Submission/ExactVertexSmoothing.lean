import Submission.NonCliqueSmoothing

/-!
Keep the precise degree charge in the nonclique-neighborhood reduction.
There is no degree upper bound in this lemma.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184
namespace ExactVertexSmoothing
open MatchingSmoothing VertexSmoothing NonCliqueSmoothing
variable {V : Type*}

def HasPieceBound [Fintype V] (B : ℕ) (G : SimpleGraph V) : Prop :=
  ∃ D : Finset G.Subgraph,
    (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
    IsDecomposition G D ∧ D.card ≤ B

set_option maxHeartbeats 800000 in
lemma nonclique_exact_cost [Fintype V] (B : ℕ) (G : SimpleGraph V)
    (he : ∀ u, Even (G.degree u)) (v : V)
    {a b : V} (hva : G.Adj v a) (hvb : G.Adj v b) (hab : a ≠ b) (hnab : ¬G.Adj a b)
    (hsmall : ∀ H : SimpleGraph (Without v),
      (∀ u, Even (H.degree u)) → HasPieceBound B H) :
    ∃ E : Finset G.Subgraph,
      (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G E ∧ 2 * (E.card + 1) ≤ 2 * B + G.degree v := by
  let A := G.induce {w | w ≠ v}
  let a' : Without v := ⟨a,hva.ne.symm⟩
  let b' : Without v := ⟨b,hvb.ne.symm⟩
  obtain ⟨M,hm,hM,hMab⟩ := exists_matching_containing (neighborsWithout G v)
    (by rw [neighborsWithout_card]; exact he v)
    (show a' ∈ neighborsWithout G v from hva)
    (show b' ∈ neighborsWithout G v from hvb)
    (fun h => hab (congrArg Subtype.val h))
  let f : apex A M ≃g G := apexIso G v M hM
  have hap : ∀ x, Even ((apex A M).degree x) := by
    intro x
    have hd := f.degree_eq x
    have hx := he (f x)
    simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hd hx ⊢
    rwa [← hd]
  have het := MixedSmoothing.even_toggled A M hm (by
    intro x
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hap x)
  obtain ⟨D,hcD,hdD,hbD⟩ := hsmall (MixedSmoothing.toggled A M) (by
    intro x
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using het x)
  have hr : 2 * M.edgeSet.ncard = G.degree v := by
    rw [← hm.support_card,hM,neighborsWithout_card]
  have hne : MixedSmoothing.newPairs A M ≠ ⊥ := by
    intro h
    have hnew : (MixedSmoothing.newPairs A M).Adj a' b' := ⟨hMab,hnab⟩
    simp only [h,bot_adj] at hnew
  obtain ⟨E,hcE,hdE,hbE⟩ := MixedSmoothing.lift_decomposition A M hm D (by
    intro H hH
    refine ⟨(hcD H hH).1,?_⟩
    intro x
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using (hcD H hH).2 x) hdD
  have hq : 0 < (D.filter (fun H =>
      (H.edgeSet ∩ (MixedSmoothing.newPairs A M).edgeSet).Nonempty)).card := by
    convert MatchingSmoothing.marked_card_pos hne D hdD using 1
  obtain ⟨F,hcF,hdF,hbF⟩ := transport_iso f E (by
    intro H hH
    refine ⟨(hcE H hH).1,?_⟩
    intro x
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using (hcE H hH).2 x) hdE
  refine ⟨F,hcF,hdF,?_⟩
  have hbE' : E.card + (D.filter (fun H =>
      (H.edgeSet ∩ (MixedSmoothing.newPairs A M).edgeSet).Nonempty)).card ≤
        D.card + M.edgeSet.ncard := by convert hbE using 1
  simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hr ⊢
  omega

set_option maxHeartbeats 800000 in
/-- No one-piece saving is asserted here; this also handles degree zero and two. -/
lemma unconditional_exact_cost [Fintype V] (B : ℕ) (G : SimpleGraph V)
    (he : ∀ u, Even (G.degree u)) (v : V)
    (hsmall : ∀ H : SimpleGraph (Without v),
      (∀ u, Even (H.degree u)) → HasPieceBound B H) :
    ∃ E : Finset G.Subgraph,
      (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G E ∧ 2 * E.card ≤ 2 * B + G.degree v := by
  let A := G.induce {w | w ≠ v}
  obtain ⟨M,hm,hM⟩ := exists_matching_support (neighborsWithout G v)
    (by rw [neighborsWithout_card]; exact he v)
  let f : apex A M ≃g G := apexIso G v M hM
  have hap : ∀ x, Even ((apex A M).degree x) := by
    intro x
    have hd := f.degree_eq x
    have hx := he (f x)
    simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hd hx ⊢
    rwa [← hd]
  have het := MixedSmoothing.even_toggled A M hm (by
    intro x
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hap x)
  obtain ⟨D,hcD,hdD,hbD⟩ := hsmall (MixedSmoothing.toggled A M) (by
    intro x
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using het x)
  have hr : 2 * M.edgeSet.ncard = G.degree v := by
    rw [← hm.support_card,hM,neighborsWithout_card]
  obtain ⟨E,hcE,hdE,hbE⟩ := MixedSmoothing.lift_decomposition A M hm D (by
    intro H hH
    refine ⟨(hcD H hH).1,?_⟩
    intro x
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using (hcD H hH).2 x) hdD
  obtain ⟨F,hcF,hdF,hbF⟩ := transport_iso f E (by
    intro H hH
    refine ⟨(hcE H hH).1,?_⟩
    intro x
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using (hcE H hH).2 x) hdE
  refine ⟨F,hcF,hdF,?_⟩
  have hbE' : E.card + (D.filter (fun H =>
      (H.edgeSet ∩ (MixedSmoothing.newPairs A M).edgeSet).Nonempty)).card ≤
        D.card + M.edgeSet.ncard := by convert hbE using 1
  simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hr ⊢
  omega

end ExactVertexSmoothing
end Erdos184
