import Submission.MinimalSingletons

/-! A fixed relative hull increase on even graphs is equivalent to the
original uniform linear decomposition assertion. Neither equivalent
assertion is established unconditionally here. -/
open Filter SimpleGraph
open scoped Classical
namespace Erdos184Work.RelativeHullCriterion
open Critical EdgeHull
set_option maxHeartbeats 1200000
universe u
variable {V : Type u} [Fintype V]

lemma bound_of_relative_boost (t : ℕ)
    (hboost : ∀ E : SimpleGraph V, (∀ v, Even (Nat.card (E.neighborSet v))) →
      (t + 1) * number E ≤ t * value E) (G : SimpleGraph V) :
    number G ≤ (t + 1) * Fintype.card V := by
  by_cases hz : value G = 0
  · have hn := number_le_value G
    omega
  obtain ⟨R,hRG,hm,hn⟩ := exists_minimal_maximizer G (Nat.pos_of_ne_zero hz)
  have hRne : R ≠ ⊥ := by
    intro h
    have he := number_bot (V := V)
    rw [h] at hn
    omega
  obtain ⟨D,hD,hdec,hcard⟩ := exists_minimum R
  obtain ⟨E,F,hER,hE,hunion,hnum,hFcard⟩ := MinimalSingletons.minimum_split D hD hdec hcard
  have hproper : E ≠ R := by
    intro heq
    apply hRne
    apply hm.edgeCritical.eq_bot_of_even
    simpa only [heq,← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hE
  have hval := MinimalSingletons.proper_hull_lt hm hER hproper
  have hb := hboost E hE
  have hs := minimal_edge_piece_count D hD hdec hcard
  have hmul := Nat.mul_le_mul_left t hval.le
  have hsmul := Nat.mul_le_mul_left (t + 1) hs
  have hRbound : number R ≤ (t + 1) * Fintype.card V := by nlinarith
  exact (number_le_value G).trans (hn ▸ hRbound)

lemma support_bound_of_uniform (C : ℝ)
    (hC : ∀ {W : Type u} [Fintype W] [DecidableEq W] (G : SimpleGraph W),
      ∃ D : Finset G.Subgraph, (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        (D.card : ℝ) ≤ C * Fintype.card W)
    (G : SimpleGraph V) : number G ≤ ⌈C⌉₊ * G.support.ncard := by
  letI : Fintype G.support := @Subtype.fintype V (fun v => v ∈ G.support)
    (fun v => Classical.propDecidable _) inferInstance
  let K := G.induce G.support
  obtain ⟨D,hD,hdec,hcard⟩ := hC K
  have hb : (D.card : ℝ) ≤ (⌈C⌉₊ : ℝ) * Fintype.card G.support :=
    hcard.trans (mul_le_mul_of_nonneg_right (Nat.le_ceil C) (Nat.cast_nonneg _))
  have hnat : D.card ≤ ⌈C⌉₊ * Fintype.card G.support := by exact_mod_cast hb
  obtain ⟨E,hE,hdecE,hcardE⟩ := Vertex.lift_decomposition_induce_support G G.support
    (Set.Subset.refl _) D hD hdec
  have hh := (number_le E hE hdecE).trans (hcardE.trans hnat)
  simpa only [← Nat.card_eq_fintype_card,Nat.card_coe_set_eq] using hh

/-- This is an equivalence/reduction, not a proof of either side. -/
lemma asymptotic_iff_relative_hull_boost :
    (∃ f : ℕ → ℝ,
      (f =O[atTop] fun n : ℕ => (n : ℝ)) ∧
      ∀ {W : Type u} [Fintype W] [DecidableEq W] (G : SimpleGraph W),
      ∃ D : Finset G.Subgraph, (∀ H ∈ D, IsCycleOrEdge H.coe) ∧
        IsDecomposition G D ∧ (D.card : ℝ) ≤ f (Fintype.card W)) ↔
    (∃ t : ℕ, ∀ {W : Type u} [Fintype W] (G : SimpleGraph W),
      (∀ v, Even (Nat.card (G.neighborSet v))) →
        (t + 1) * number G ≤ t * value G) := by
  constructor
  · intro h
    obtain ⟨C,hC⟩ := asymptotic_iff_uniform.mp h
    refine ⟨6 * ⌈C⌉₊,?_⟩
    intro W _ G he
    exact StarHullBoost.relative_boost_of_support_bound G he ⌈C⌉₊
      (support_bound_of_uniform C hC G)
  · rintro ⟨t,ht⟩
    apply asymptotic_iff_uniform.mpr
    refine ⟨((t + 1 : ℕ) : ℝ),?_⟩
    intro W _ _ G
    obtain ⟨D,hD,hdec,hcard⟩ := exists_minimum G
    refine ⟨D,hD,hdec,?_⟩
    have hb := bound_of_relative_boost t (fun E hE => ht E hE) G
    rw [← hcard] at hb
    exact_mod_cast hb

end Erdos184Work.RelativeHullCriterion
#print axioms Erdos184Work.RelativeHullCriterion.asymptotic_iff_relative_hull_boost
