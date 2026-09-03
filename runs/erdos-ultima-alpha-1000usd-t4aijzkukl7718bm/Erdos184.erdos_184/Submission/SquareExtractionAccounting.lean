import Submission.SquareDiscardBudget

/-! Actual square-deletion/core-extraction accounting. The discarded graph is
retained explicitly; no uniform bound on its decomposition number is asserted. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.SquareExtractionAccounting
open Critical EvenCore Rigidity SquarePieces SquareDiscardBudget
set_option maxHeartbeats 1600000
variable {V : Type*} [Fintype V]

def NoSquare (G : SimpleGraph V) : Prop :=
  ∀ u (p : G.Walk u u), p.IsCycle → p.length ≠ 4

private lemma even_union (S T : SimpleGraph V)
    (hd : Disjoint S.edgeSet T.edgeSet)
    (hs : ∀ v, Even (S.degree v)) (ht : ∀ v, Even (T.degree v)) :
    ∀ v, Even ((S ⊔ T).degree v) := by
  have he : (S ⊔ T) \ S = T := by
    ext x y
    change ((S.Adj x y ∨ T.Adj x y) ∧ ¬ S.Adj x y) ↔ T.Adj x y
    have hn : ¬ (S.Adj x y ∧ T.Adj x y) := by
      rintro ⟨hS,hT⟩
      exact Set.disjoint_left.mp hd (show s(x,y) ∈ S.edgeSet from hS) hT
    tauto
  intro v
  have h := degree_sdiff_add (S ⊔ T) S le_sup_left v
  have hh := (ht v).add (hs v)
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at h hh ⊢
  rw [he] at h
  rwa [← h]

private lemma union_card (S T : SimpleGraph V)
    (hd : Disjoint S.edgeSet T.edgeSet) :
    Nat.card (S ⊔ T).edgeSet = Nat.card S.edgeSet + Nat.card T.edgeSet := by
  simp only [SimpleGraph.edgeSet_sup, Nat.card_coe_set_eq]
  exact Set.ncard_union_eq hd

/-- Extract a square-free final core, keeping the union of the removed squares
as a separate even graph. Additional even edges may have been discarded. -/
lemma exists_extraction (G : SimpleGraph V) (he : ∀ v, Even (G.degree v)) :
    ∃ (S R : SimpleGraph V) (k : ℕ),
      S ≤ G ∧ R ≤ G ∧ Disjoint S.edgeSet R.edgeSet ∧
      (∀ v, Even (S.degree v)) ∧ (∀ v, Even (R.degree v)) ∧
      NoSquare R ∧ EvenMinimal R ∧ Nat.card S.edgeSet = 4*k ∧
      number G = k + number R := by
  induction hm : Nat.card G.edgeSet using Nat.strong_induction_on generalizing G with
  | h m ih =>
    obtain ⟨Q,hQG,hQe,hQn,hQm,hQc⟩ := exists_even_minimal_core G he
    have hQe' : ∀ v, Even (Q.degree v) := by
      simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
        using hQe
    by_cases hno : NoSquare Q
    · refine ⟨⊥,Q,0,bot_le,hQG,by simp,?_,hQe',hno,hQm,by simp,?_⟩
      · intro v
        simp [← SimpleGraph.card_neighborSet_eq_degree]
      · simpa using hQn.symm
    · obtain ⟨u,p,hp,hl⟩ : ∃ u, ∃ p : Q.Walk u u, p.IsCycle ∧ p.length = 4 := by
        unfold NoSquare at hno
        push_neg at hno
        exact hno
      let C := p.toSubgraph.spanningCoe
      let E := Q \ C
      have hCQ : C ≤ Q := p.toSubgraph.spanningCoe_le
      have hEQ : E ≤ Q := sdiff_le
      have hEe : ∀ v, Even (E.degree v) := delete_cycle_even hQe' hp
      have hlt := delete_cycle_card_lt hp
      have hle := Finset.card_le_card (SimpleGraph.edgeFinset_mono hQG)
      have hsmall : Nat.card E.edgeSet < m := by
        simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hlt hle
        change Nat.card E.edgeSet < Nat.card Q.edgeSet at hlt
        omega
      obtain ⟨S,R,k,hSE,hRE,hd,hSe,hRe,hRn,hRm,hSc,hkn⟩ :=
        ih _ hsmall E (by
          simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
            using hEe) rfl
      have hSC : Disjoint S.edgeSet C.edgeSet := by
        apply Set.disjoint_left.mpr
        intro e hs hc
        have hh := SimpleGraph.edgeSet_mono hSE hs
        rw [show E = Q \ C from rfl, SimpleGraph.edgeSet_sdiff] at hh
        exact hh.2 hc
      have hCR : Disjoint C.edgeSet R.edgeSet := by
        apply Set.disjoint_left.mpr
        intro e hc hr
        have hh := SimpleGraph.edgeSet_mono hRE hr
        rw [show E = Q \ C from rfl, SimpleGraph.edgeSet_sdiff] at hh
        exact hh.2 hc
      have hCe : ∀ v, Even (C.degree v) := cycle_spanning_even Q hp
      have hCc : Nat.card C.edgeSet = 4 := by
        have hh := (cycle_edge_count Q hp).trans hl
        simpa only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] using hh
      have hcount := union_card C S hSC.symm
      have hn := hQc u p hp
      change number Q = number E + 1 at hn
      refine ⟨C ⊔ S,R,k+1,sup_le (hCQ.trans hQG) (hSE.trans (hEQ.trans hQG)),
        hRE.trans (hEQ.trans hQG),?_,?_,hRe,hRn,hRm,?_,?_⟩
      · rw [SimpleGraph.edgeSet_sup]
        exact hCR.sup_left hd
      · simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
          using even_union C S hSC.symm hCe hSe
      · rw [hcount,hCc,hSc]
        omega
      · omega

lemma number_le_of_noSquare (G : SimpleGraph V) (hno : NoSquare G) :
    number G ≤ 6 * Fintype.card V := by
  obtain ⟨D,hD,hd,hc⟩ := no_four_cycle_decomposition_linear G hno
  exact (number_le D hD hd).trans hc

/-- Unconditional accounting for an even graph. `J` is the entire union of
all discarded edges, not one individual discard. The last term remains. -/
lemma exists_discard_budget (G : SimpleGraph V) (he : ∀ v, Even (G.degree v)) :
    ∃ J : SimpleGraph V, J ≤ G ∧ (∀ v, Even (J.degree v)) ∧
      number G ≤ 15 * Fintype.card V + 5 * number J ∧
      Nat.card J.edgeSet + 4 * number G ≤
        Nat.card G.edgeSet + 24 * Fintype.card V := by
  obtain ⟨S,R,k,hSG,hRG,hd,hSe,hRe,hRn,hRm,hSc,hkn⟩ := exists_extraction G he
  let U := S ⊔ R
  let J := G \ U
  have hUG : U ≤ G := sup_le hSG hRG
  have hUe : ∀ v, Even (U.degree v) := by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using even_union S R hd hSe hRe
  have hJe : ∀ v, Even (J.degree v) := by
    have hh := sdiff_even he hUG (by
      simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
        using hUe)
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using hh
  have hJd : Disjoint U.edgeSet J.edgeSet := by
    change Disjoint U.edgeSet (G \ U).edgeSet
    rw [SimpleGraph.edgeSet_sdiff]
    exact Set.disjoint_sdiff_right
  have hcover : U ⊔ J = G := by
    change U ⊔ (G \ U) = G
    rw [sup_comm]
    exact sdiff_sup_cancel hUG
  have h₁ := number_union_le S R hd
  have h₂ := number_union_le U J hJd
  rw [hcover] at h₂
  have h₃ := five_mul_number_le_edges_add_nine_card hSe
  have h₄ := number_le_of_noSquare R hRn
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at h₃
  rw [hSc] at h₃
  have hV : Nat.card V = Fintype.card V := Nat.card_eq_fintype_card
  have hbudget : number G ≤ 15 * Fintype.card V + 5 * number J := by
    change number U ≤ number S + number R at h₁
    omega
  have hc := union_card U J hJd
  rw [hcover] at hc
  have hUR := union_card S R hd
  change Nat.card U.edgeSet = Nat.card S.edgeSet + Nat.card R.edgeSet at hUR
  rw [hSc] at hUR
  have hecard : Nat.card J.edgeSet + 4 * number G ≤
      Nat.card G.edgeSet + 24 * Fintype.card V := by
    omega
  refine ⟨J,sdiff_le,?_,hbudget,hecard⟩
  simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
    using hJe


/-- Above the square-free threshold, the discarded edges contain a strictly
smaller even-minimal core with the stated quantitative guarantees. The factor
five prevents this recurrence alone from giving a uniform linear bound. -/
lemma core_descent (G : SimpleGraph V) (he : ∀ v, Even (G.degree v))
    (hm : EvenMinimal G) (hlarge : 6 * Fintype.card V < number G) :
    ∃ R : SimpleGraph V, R ≤ G ∧ (∀ v, Even (R.degree v)) ∧ EvenMinimal R ∧
      number R < number G ∧
      number G ≤ 15 * Fintype.card V + 5 * number R ∧
      Nat.card R.edgeSet + 4 * number G ≤
        Nat.card G.edgeSet + 24 * Fintype.card V := by
  obtain ⟨J,hJG,hJe,hb,hc⟩ := exists_discard_budget G he
  obtain ⟨R,hRJ,hRe,hn,hRm,_⟩ := exists_even_minimal_core J hJe
  have hRG := hRJ.trans hJG
  have hmR := Finset.card_le_card (SimpleGraph.edgeFinset_mono hRJ)
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hmR
  have hstrict : Nat.card R.edgeSet < Nat.card G.edgeSet := by omega
  have hRe' : ∀ v, Even (R.degree v) := by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using hRe
  have hnum := hm R hRG (by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using hRe) (by
    simpa only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] using hstrict)
  exact ⟨R,hRG,hRe',hRm,hnum,by omega,by omega⟩

end Erdos184Work.SquareExtractionAccounting
#print axioms Erdos184Work.SquareExtractionAccounting.exists_extraction
#print axioms Erdos184Work.SquareExtractionAccounting.exists_discard_budget

#print axioms Erdos184Work.SquareExtractionAccounting.core_descent
