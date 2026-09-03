import Submission.EvenCycleFactorization
import Submission.LowCountCritical

/-! Integer thresholds for the fractional envelope. These estimates are
restricted comparisons, not a uniform integral rounding theorem. -/
open SimpleGraph
open scoped Classical BigOperators
namespace Erdos184.EnvelopeFactorBounds
open FractionalEnvelope CycleNumberSubmodularity CountCritical
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 1000000

lemma degree_bound_of_envelope_lt {G H : SimpleGraph V} {r : ℕ}
    (hHG : H ≤ G) (he : ∀ v, Even (H.degree v))
    (hb : envelope G < (r : ℝ) + 1) (v : V) : H.degree v ≤ 2*r := by
  have h₁ := degree_le_twice_optimum H he v
  have h₂ := optimum_le_envelope hHG he
  obtain ⟨d,hd⟩ := he v
  have hd' : (H.degree v : ℝ) = 2 * (d : ℝ) := by exact_mod_cast (by omega : H.degree v = 2*d)
  have hlt : (d : ℝ) < (r : ℝ) + 1 := by linarith
  have hn : d < r+1 := by exact_mod_cast hlt
  omega

lemma cycles_of_even_degree_le_two {H : SimpleGraph V}
    (he : ∀ v, Even (H.degree v)) (hd : ∀ v, H.degree v ≤ 2) : H.IsCycles := by
  intro v hn
  have hp := H.degree_pos_iff_nonempty.mpr hn
  obtain ⟨d,heq⟩ := he v
  have hh := hd v
  have hval : H.degree v = 2 := by
    simp only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hp heq hh ⊢
    omega
  simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card,
    Nat.card_coe_set_eq] using hval

lemma integral_le_one_of_fractional_lt_two (G : SimpleGraph V)
    (hb : envelope G < 2) : CycleEnvelope.envelope G ≤ 1 := by
  apply CycleEnvelope.envelope_le
  intro H hHG he
  have hd : ∀ v, H.degree v ≤ 2 := by
    intro v
    simpa using degree_bound_of_envelope_lt (r := 1) hHG he (by norm_num; exact hb) v
  have hx := CycleFactors.optimum_eq_number (cycles_of_even_degree_le_two he hd)
  have hh := optimum_le_envelope hHG he
  rw [hx] at hh
  have hl : (cycleNumber H : ℝ) < 2 := hh.trans_lt hb
  have hn : cycleNumber H < 2 := by exact_mod_cast hl
  omega

lemma integral_le_four_of_fractional_lt_three (G : SimpleGraph V)
    (hb : envelope G < 3) : CycleEnvelope.envelope G ≤ 4 := by
  apply CycleEnvelope.envelope_le
  intro H hHG he
  have hd : ∀ v, H.degree v ≤ 4 := by
    intro v
    simpa using degree_bound_of_envelope_lt (r := 2) hHG he (by norm_num; exact hb) v
  obtain ⟨A,B,hA,hB,hdis,hcov⟩ := EvenCycleFactorization.exists_two_factors H he hd
  have hAH : A ≤ H := edgeSet_subset_edgeSet.mp (by rw [← hcov]; exact Set.subset_union_left)
  have hBH : B ≤ H := edgeSet_subset_edgeSet.mp (by rw [← hcov]; exact Set.subset_union_right)
  have bound (X : SimpleGraph V) (hX : X.IsCycles) (hle : X ≤ H) : cycleNumber X ≤ 2 := by
    have hh := optimum_le_envelope (hle.trans hHG) (CycleFactors.cycles_even hX)
    rw [CycleFactors.optimum_eq_number hX] at hh
    have hl : (cycleNumber X : ℝ) < 3 := hh.trans_lt hb
    have hn : cycleNumber X < 3 := by exact_mod_cast hl
    omega
  exact (CycleFactors.number_le_add hcov hdis (CycleFactors.cycles_even hA)
    (CycleFactors.cycles_even hB)).trans (by have := bound A hA hAH; have := bound B hB hBH; omega)

lemma fractional_ge_two_of_integral_ge_two (G : SimpleGraph V)
    (h : 2 ≤ CycleEnvelope.envelope G) : 2 ≤ envelope G := by
  by_contra! hn
  have := integral_le_one_of_fractional_lt_two G hn
  omega

lemma fractional_ge_three_of_integral_ge_five (G : SimpleGraph V)
    (h : 5 ≤ CycleEnvelope.envelope G) : 3 ≤ envelope G := by
  by_contra! hn
  have := integral_le_four_of_fractional_lt_three G hn
  omega

/-- The rooted comparison holds for critical count at most six. The count
restriction is essential to this proof and is not claimed in general. -/
lemma rooted_critical_count_le_six {G : SimpleGraph V} {k : ℕ}
    (hG : IsCountCritical k G) (hk : k ≤ 6) (e : Sym2 V) (he : e ∈ G.edgeSet) :
    (k : ℝ) ≤ envelope (G.deleteEdges {e}) + RootedEnvelopeProfiles.through G e := by
  by_cases hd : ∀ v, G.degree v ≤ 4
  · simpa only [hG.2.1] using EvenCycleFactorization.rooted_degree_four G hG.1 hd e he
  push_neg at hd
  obtain ⟨v,hv⟩ := hd
  obtain ⟨d,hd⟩ := hG.1 v
  have hdeg : 6 ≤ G.degree v := by omega
  have h₁ := degree_le_twice_optimum G hG.1 v
  have h₂ := RootedEnvelopeProfiles.optimum_le_through le_rfl hG.1 he
  have hdeg' : (6 : ℝ) ≤ G.degree v := by exact_mod_cast hdeg
  have ht : 3 ≤ RootedEnvelopeProfiles.through G e := by linarith
  have ha := envelope_nonneg (G.deleteEdges {e})
  have hdel := CycleEnvelope.critical_delete_edge hG e he
  by_cases hsmall : k ≤ 3
  · have hk' : (k : ℝ) ≤ 3 := by exact_mod_cast hsmall
    linarith
  by_cases hmid : k ≤ 5
  · have hh := fractional_ge_two_of_integral_ge_two (G.deleteEdges {e}) (by omega)
    have hk' : (k : ℝ) ≤ 5 := by exact_mod_cast hmid
    linarith
  · have hh := fractional_ge_three_of_integral_ge_five (G.deleteEdges {e}) (by omega)
    have hk' : (k : ℝ) ≤ 6 := by exact_mod_cast hk
    linarith

end Erdos184.EnvelopeFactorBounds
