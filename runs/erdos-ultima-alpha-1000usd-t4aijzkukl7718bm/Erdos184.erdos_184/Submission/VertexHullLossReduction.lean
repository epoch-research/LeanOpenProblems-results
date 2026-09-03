import Submission.VertexSeparatorReduction

/-! A necessary vertex-deletion obstruction to the asymptotic conjecture.
A uniform loss bound on a suitably chosen vertex of each globally minimal
core would suffice. No such loss bound is asserted in this file. -/

open Filter SimpleGraph
open scoped Classical

namespace Erdos184Work.VertexHullLoss
open Critical EdgeHull
set_option maxHeartbeats 1200000
universe u

/-- A selective bound, not a claim about every vertex. -/
def Property (C : ℕ) : Prop :=
  ∀ (V : Type u) [Fintype V] (G : SimpleGraph V),
    Minimal G → Nonempty V →
      ∃ v : V, number G ≤ value (G.induce ({v}ᶜ : Set V)) + C

lemma uniform_of_property (C : ℕ) (h : Property.{u} C) :
    ∀ (V : Type u) [Fintype V] (G : SimpleGraph V),
      number G ≤ C * Fintype.card V := by
  have main : ∀ n : ℕ, ∀ (V : Type u) [Fintype V] (G : SimpleGraph V),
      Fintype.card V = n → number G ≤ C * Fintype.card V := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro V iV G hn
      by_cases hz : value G = 0
      · have hg := number_le_value G
        omega
      obtain ⟨R,hRG,hm,hR⟩ := exists_minimal_maximizer G (Nat.pos_of_ne_zero hz)
      have hV : Nonempty V := by
        by_contra he
        haveI : IsEmpty V := not_nonempty_iff.mp he
        have hr : R = ⊥ := by ext x; exact isEmptyElim x
        have hh : number R = 0 := by rw [hr,number_bot]
        omega
      obtain ⟨v,hv⟩ := h V R hm hV
      have hc : Fintype.card ({v}ᶜ : Set V) + 1 = Fintype.card V := by
        have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr hV
        rw [Fintype.card_compl_set]
        simp only [Fintype.card_unique]
        omega
      have hsmall : Fintype.card ({v}ᶜ : Set V) < n := by omega
      have hb : value (R.induce ({v}ᶜ : Set V)) ≤
          C * Fintype.card ({v}ᶜ : Set V) := by
        apply (value_le_iff _ _).mpr
        intro S _
        exact ih _ hsmall _ S rfl
      have hmul := congrArg (C * ·) hc
      simp only [Nat.mul_add, Nat.mul_one] at hmul
      have hg := number_le_value G
      omega
  intro V _ G
  exact main _ V G rfl

lemma asymptotic_of_property (C : ℕ) (h : Property.{u} C) :
    ∃ f : ℕ → ℝ,
      (f =O[atTop] fun n : ℕ => (n : ℝ)) ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        (D.card : ℝ) ≤ f (Fintype.card V) := by
  apply asymptotic_iff_uniform.mpr
  refine ⟨(C : ℝ), ?_⟩
  intro V _ _ G
  obtain ⟨D,hD,hd,hcard⟩ := exists_minimum G
  refine ⟨D,hD,hd,?_⟩
  have hb := uniform_of_property C h V G
  rw [← hcard] at hb
  exact_mod_cast hb

/-- Failure of the original conjecture would force globally minimal graphs
whose hull loss is arbitrarily large at EVERY vertex. This is an implication,
not a proof that such graphs exist. -/
lemma obstruction_of_asymptotic_failure
    (hbad : ¬ (∃ f : ℕ → ℝ,
      (f =O[atTop] fun n : ℕ => (n : ℝ)) ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        (D.card : ℝ) ≤ f (Fintype.card V))) (C : ℕ) :
    ∃ (V : Type u) (_ : Fintype V) (G : SimpleGraph V),
      Minimal G ∧ Nonempty V ∧
        ∀ v : V, value (G.induce ({v}ᶜ : Set V)) + C < number G := by
  have hn : ¬ Property.{u} C := fun h => hbad (asymptotic_of_property C h)
  unfold Property at hn
  push_neg at hn
  exact hn

end Erdos184Work.VertexHullLoss

#print axioms Erdos184Work.VertexHullLoss.uniform_of_property
#print axioms Erdos184Work.VertexHullLoss.obstruction_of_asymptotic_failure
