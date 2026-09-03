import Submission.MinimalSingletons
open SimpleGraph
open scoped Classical
namespace Erdos184Work.ProbeRelative
open Critical
universe u
variable {V : Type u} [Fintype V]
set_option maxHeartbeats 200000
set_option diagnostics true
lemma support_bound (C : ℝ)
    (hC : ∀ {W : Type u} [Fintype W] [DecidableEq W] (G : SimpleGraph W),
      ∃ D : Finset G.Subgraph, (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        (D.card : ℝ) ≤ C * Fintype.card W)
    (G : SimpleGraph V) : number G ≤ ⌈C⌉₊ * G.support.ncard := by
  letI : Fintype G.support := @Subtype.fintype V (fun v => v ∈ G.support)
    (fun v => Classical.propDecidable _) inferInstance
  let K := G.induce G.support
  obtain ⟨D,hD,hdec,hcard⟩ := hC K
  trace "obtained D"
  have hb : (D.card : ℝ) ≤ (⌈C⌉₊ : ℝ) * Fintype.card G.support :=
    hcard.trans (mul_le_mul_of_nonneg_right (Nat.le_ceil C) (Nat.cast_nonneg _))
  trace "cast bound"
  have hnat : D.card ≤ ⌈C⌉₊ * Fintype.card G.support := by exact_mod_cast hb
  trace "nat bound"
  obtain ⟨E,hE,hdecE,hcardE⟩ := lift_decomposition_induce_support G G.support
    (Set.Subset.refl _) D hD hdec
  trace "lifted"
  have hh := (number_le E hE hdecE).trans (hcardE.trans hnat)
  trace "number bound"
  simpa only [← Nat.card_eq_fintype_card,Nat.card_coe_set_eq] using hh
end Erdos184Work.ProbeRelative
#print axioms Erdos184Work.ProbeRelative.support_bound
