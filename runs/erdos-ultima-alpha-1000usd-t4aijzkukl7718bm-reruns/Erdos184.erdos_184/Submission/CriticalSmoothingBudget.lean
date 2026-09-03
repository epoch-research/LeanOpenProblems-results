import Submission.CliqueSmoothing

/-!
An exact necessary budget for every smoothing of a critical apex. The bound
identifies, but does not prove, the marked-piece saving needed at high degree.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184
namespace CriticalSmoothingBudget
open MatchingSmoothing VertexSmoothing GlobalVertexMinimal

variable {V : Type*} [Fintype V]

lemma apex_budget (C : ℕ) (A M : SimpleGraph V) (hm : IsMatching M)
    (hbad : ¬HasCardBound C (apex A M))
    (D : Finset (MixedSmoothing.toggled A M).Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition (MixedSmoothing.toggled A M) D) :
    C * Fintype.card (Option V) + 1 +
      (D.filter (fun H => (H.edgeSet ∩ (MixedSmoothing.newPairs A M).edgeSet).Nonempty)).card
      ≤ D.card + M.edgeSet.ncard := by
  obtain ⟨E,hcE,hdE,hbE⟩ := MixedSmoothing.lift_decomposition A M hm D hc hd
  have hbadE : C * Fintype.card (Option V) < E.card := by
    by_contra! h
    apply hbad
    refine ⟨E,?_,hdE,h⟩
    intro H hH
    refine ⟨(hcE H hH).1,?_⟩
    intro x
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using (hcE H hH).2 x
  have hbE' : E.card + (D.filter (fun H =>
      (H.edgeSet ∩ (MixedSmoothing.newPairs A M).edgeSet).Nonempty)).card ≤
        D.card + M.edgeSet.ncard := by convert hbE using 1
  omega

lemma bounded_apex_budget (C : ℕ) (A M : SimpleGraph V) (hm : IsMatching M)
    (hbad : ¬HasCardBound C (apex A M))
    (D : Finset (MixedSmoothing.toggled A M).Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition (MixedSmoothing.toggled A M) D)
    (hb : D.card ≤ C * Fintype.card V) :
    C + 1 + (D.filter (fun H =>
      (H.edgeSet ∩ (MixedSmoothing.newPairs A M).edgeSet).Nonempty)).card
      ≤ M.edgeSet.ncard := by
  have hh := apex_budget C A M hm hbad D hc hd
  rw [Fintype.card_option,Nat.mul_add,Nat.mul_one] at hh
  omega

universe u
set_option maxHeartbeats 800000 in
/-- Global minimality provides the bounded residual decomposition; every
such decomposition obeys the necessary budget. -/
lemma vertex_matching_budget {V : Type u} [Fintype V]
    {C : ℕ} {G : SimpleGraph V} (hG : IsVertexMinimal C G) (v : V)
    (M : SimpleGraph (Without v)) (hm : IsMatching M)
    (hM : M.support = neighborsWithout G v) :
    ∃ D : Finset (MixedSmoothing.toggled (G.induce {w | w ≠ v}) M).Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition (MixedSmoothing.toggled (G.induce {w | w ≠ v}) M) D ∧
      D.card ≤ C * Fintype.card (Without v) ∧
      C + 1 + (D.filter (fun H => (H.edgeSet ∩
        (MixedSmoothing.newPairs (G.induce {w | w ≠ v}) M).edgeSet).Nonempty)).card
        ≤ M.edgeSet.ncard := by
  let A := G.induce {w | w ≠ v}
  let f : apex A M ≃g G := apexIso G v M hM
  have heA : ∀ x, Even ((apex A M).degree x) := by
    intro x
    have hx := hG.1 (f x)
    have hd := f.degree_eq x
    simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hx hd ⊢
    rwa [← hd]
  have het := MixedSmoothing.even_toggled A M hm (by
    intro x
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using heA x)
  obtain ⟨D,hcD,hdD,hbD⟩ := hG.2.2 (MixedSmoothing.toggled A M)
    (Fintype.card_subtype_lt (x := v) (by simp)) (by
      intro x
      simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using het x)
  have hbad : ¬HasCardBound C (apex A M) := fun h => hG.2.1 (HasCardBound.of_iso f h)
  have hbudget := bounded_apex_budget C A M hm hbad D (by
    intro H hH
    refine ⟨(hcD H hH).1,?_⟩
    intro x
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using (hcD H hH).2 x) hdD hbD
  refine ⟨D,?_,hdD,hbD,?_⟩
  · intro H hH
    refine ⟨(hcD H hH).1,?_⟩
    intro x
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using (hcD H hH).2 x
  · convert hbudget using 1

end CriticalSmoothingBudget
end Erdos184
