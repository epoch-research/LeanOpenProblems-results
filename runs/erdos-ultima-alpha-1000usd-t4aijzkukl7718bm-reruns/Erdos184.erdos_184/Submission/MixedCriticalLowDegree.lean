import Submission.MixedCritical
import Submission.CriticalVertexLoss

/-! A conditional linear bound from a bounded positive degree in mixed-critical
restrictions. The structural degree hypothesis is not proved here. -/
open SimpleGraph
open scoped Classical
namespace Erdos184.MixedCritical
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 1000000

lemma number_le_delete_vertex (G : SimpleGraph V) (v : V) :
    number G ≤ number (G.deleteIncidenceSet v) + G.degree v := by
  have he : (G \ G.deleteIncidenceSet v).edgeSet = G.incidenceSet v := by
    rw [edgeSet_sdiff, edgeSet_deleteIncidenceSet]
    ext e
    have hsub := G.incidenceSet_subset v
    constructor
    · rintro ⟨hG,hn⟩
      by_contra hi
      exact hn ⟨hG,hi⟩
    · intro hi
      exact ⟨hsub hi,fun h => h.2 hi⟩
  have hcard : (G.incidenceSet v).ncard = G.degree v := by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq] using
      G.card_incidenceSet_eq_degree v
  have h := number_le_restriction_add_edges (G.deleteIncidenceSet_le v)
  rwa [he,hcard] at h

/-- Only a favorable vertex in each critical restriction is needed. Neither
vertex deletion nor a whole cycle-deleted remainder is assumed critical. -/
lemma number_bound_of_critical_low_degree (G : SimpleGraph V) (C : ℕ)
    (hlow : ∀ H : SimpleGraph V, H ≤ G → ∀ k : ℕ, 0 < k → IsCritical k H →
      ∃ v ∈ H.support, H.degree v ≤ C) :
    number G ≤ C * G.support.ncard := by
  generalize hn : G.support.ncard = n
  induction n using Nat.strong_induction_on generalizing G with
  | h n ih =>
    by_cases hz : number G = 0
    · rw [hz]; exact Nat.zero_le _
    obtain ⟨H,hHG,hH⟩ := extract G (number G) (Nat.pos_of_ne_zero hz) le_rfl
    obtain ⟨v,hv,hd⟩ := hlow H hHG _ (Nat.pos_of_ne_zero hz) hH
    have hdrop := CycleEnvelope.support_delete_vertex_card H v hv
    have hs := Set.ncard_le_ncard (SimpleGraph.support_mono hHG)
    have hlt : (H.deleteIncidenceSet v).support.ncard < n := by omega
    have hb := ih _ hlt (H.deleteIncidenceSet v) (by
      intro A hAR k hk hA
      exact hlow A (hAR.trans ((H.deleteIncidenceSet_le v).trans hHG)) k hk hA) rfl
    have hstep := number_le_delete_vertex H v
    rw [hH.1] at hstep
    have hmul := Nat.mul_le_mul_left C
      (show (H.deleteIncidenceSet v).support.ncard + 1 ≤ n by omega)
    rw [Nat.mul_add,Nat.mul_one] at hmul
    omega

universe u
/-- An explicit sufficient hypothesis, not a proof of that hypothesis. -/
lemma conjecture_of_mixed_critical_low_degree (C : ℕ)
    (hlow : ∀ {V : Type u} [Fintype V] (G : SimpleGraph V) (k : ℕ),
      0 < k → IsCritical k G → ∃ v ∈ G.support, G.degree v ≤ C) :
    ∃ f : ℕ → ℝ,
      (f =O[Filter.atTop] fun n : ℕ => (n : ℝ)) ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        (D.card : ℝ) ≤ f (Fintype.card V) := by
  apply conjecture_iff_even_bound.mpr
  refine ⟨(C : ℝ),?_⟩
  intro V _ _ G _
  obtain ⟨D,hc,hd,hcard⟩ := minimum_exists G
  have hb := number_bound_of_critical_low_degree G C
    (fun H _ k hk hH => hlow H k hk hH)
  have hs : G.support.ncard ≤ Fintype.card V := by
    simpa using Set.ncard_le_ncard (Set.subset_univ G.support)
  refine ⟨D,hc,hd,?_⟩
  rw [hcard]
  exact_mod_cast hb.trans (Nat.mul_le_mul_left C hs)

end Erdos184.MixedCritical
