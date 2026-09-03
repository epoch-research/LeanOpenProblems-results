import Submission.GreedyNonlinearGuards
import Submission.GreedyTrackedState

/-! The combined nonlinear all-prefix guard transfers to the tracked kernel. -/
namespace Erdos773.GreedyNonlinearGuardTails
open Finset GreedyHypergraphState GreedyCodegreeDrift GreedyCommonNeighbors
open GreedyConfigurationTails StoppedGreedyMoments FourUniformRegularization HypergraphDegreeTrim
open GreedyTrackedState FiniteKernelCrossing
set_option maxHeartbeats 2500000
set_option exponentiation.threshold 1024
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

def cost (H : Finset (Finset α)) (C B2 B3 : ℕ) (I : Finset α) : ℝ :=
  GreedyLocalErrorCertificates.badCost H C I +
  (∑ u : α, event (GreedyPromotionTails.prefixBad H u B2) I) +
  (∑ u : α, event (GreedyHigherPromotionTails.prefixBad H u B3) I)

def auxiliaryBad (H : Finset (Finset α)) (C B2 B3 : ℕ) (I : Finset α) : Prop :=
  1 ≤ cost H C B2 B3 I

lemma cost_nonneg (H : Finset (Finset α)) (C B2 B3 : ℕ) (I : Finset α) :
    0 ≤ cost H C B2 B3 I := by
  unfold cost GreedyLocalErrorCertificates.badCost
  exact add_nonneg (add_nonneg (add_nonneg
    (sum_nonneg (fun _ _ => event_nonneg _ _))
    (sum_nonneg (fun _ _ => event_nonneg _ _)))
    (sum_nonneg (fun _ _ => event_nonneg _ _)))
    (sum_nonneg (fun _ _ => event_nonneg _ _))

omit [Fintype α] [DecidableEq α] in
lemma event_le_event {P Q : Finset α → Prop} {I J : Finset α} (h : P I → Q J) :
    event P I ≤ event Q J := by
  classical
  by_cases hp : P I
  · simp only [event,if_pos hp,if_pos (h hp),le_refl]
  · simpa only [event,if_neg hp] using event_nonneg Q J

/-- Monotone in the selected carrier, antitone in the three thresholds. -/
lemma cost_mono {H : Finset (Finset α)} {I J : Finset α} (hIJ : I ⊆ J)
    {C D B2 D2 B3 D3 : ℕ} (hC : D ≤ C) (h2 : D2 ≤ B2) (h3 : D3 ≤ B3) :
    cost H C B2 B3 I ≤ cost H D D2 D3 J := by
  unfold cost GreedyLocalErrorCertificates.badCost
  apply add_le_add
  · apply add_le_add
    · apply add_le_add
      · apply sum_le_sum
        intro u hu
        apply event_le_event
        rintro ⟨S,hSI,hbad⟩
        exact ⟨S,hSI.trans hIJ,hC.trans_lt hbad⟩
      · apply sum_le_sum
        intro uv huv
        apply event_le_event
        rintro ⟨S,hSI,hu,hv,hbad⟩
        exact ⟨S,hSI.trans hIJ,hu,hv,hC.trans_lt hbad⟩
    · apply sum_le_sum
      intro u hu
      apply event_le_event
      rintro ⟨S,hSI,hbad⟩
      exact ⟨S,hSI.trans hIJ,h2.trans_lt hbad⟩
  · apply sum_le_sum
    intro u hu
    apply event_le_event
    rintro ⟨S,hSI,hbad⟩
    exact ⟨S,hSI.trans hIJ,h3.trans_lt hbad⟩

lemma auxiliaryBad_mono (H : Finset (Finset α)) (C B2 B3 : ℕ) {I J : Finset α}
    (hIJ : I ⊆ J) : auxiliaryBad H C B2 B3 I → auxiliaryBad H C B2 B3 J := by
  exact fun h => h.trans (cost_mono hIJ le_rfl le_rfl le_rfl)

/-- Avoiding the cost event supplies each local guard on every subset. -/
theorem controls_of_not_bad {H : Finset (Finset α)} {C B2 B3 : ℕ} {I : Finset α}
    (h : ¬auxiliaryBad H C B2 B3 I) :
    (∀ J ⊆ I, ∀ u, duplicateExcess H J u ≤ C) ∧
    (∀ J ⊆ I, ∀ u ∈ available H J, ∀ v ∈ available H J, u ≠ v → commonDegree H J u v ≤ C) ∧
    (∀ J ⊆ I, ∀ u, promotionDefect H J 2 u ≤ B2) ∧
    (∀ J ⊆ I, ∀ u, promotionDefect H J 3 u ≤ B3) := by
  have hsmall : cost H C B2 B3 I < 1 := lt_of_not_ge h
  have h₀ := sum_nonneg (s := (univ : Finset α)) (fun u _ => event_nonneg (GreedyLocalDuplicateTails.prefixBad H u C) I)
  have h₁ := sum_nonneg (s := (univ : Finset α).offDiag) (fun uv _ => event_nonneg (GreedyCommonNeighbors.prefixBad H uv.1 uv.2 C) I)
  have h₂ := sum_nonneg (s := (univ : Finset α)) (fun u _ => event_nonneg (GreedyPromotionTails.prefixBad H u B2) I)
  have h₃ := sum_nonneg (s := (univ : Finset α)) (fun u _ => event_nonneg (GreedyHigherPromotionTails.prefixBad H u B3) I)
  unfold cost GreedyLocalErrorCertificates.badCost at hsmall
  have hh₀ : (∑ u : α, event (GreedyLocalDuplicateTails.prefixBad H u C) I) < 1 := by linarith only [hsmall,h₀,h₁,h₂,h₃]
  have hh₁ : (∑ uv ∈ (univ : Finset α).offDiag, event (GreedyCommonNeighbors.prefixBad H uv.1 uv.2 C) I) < 1 := by linarith only [hsmall,h₀,h₁,h₂,h₃]
  have hh₂ : (∑ u : α, event (GreedyPromotionTails.prefixBad H u B2) I) < 1 := by linarith only [hsmall,h₀,h₁,h₂,h₃]
  have hh₃ : (∑ u : α, event (GreedyHigherPromotionTails.prefixBad H u B3) I) < 1 := by linarith only [hsmall,h₀,h₁,h₂,h₃]
  refine ⟨?_,?_,?_,?_⟩
  · intro J hJI u
    apply le_of_not_gt
    intro hb
    exact GreedyNonlinearGuards.event_sum_excludes _ _ I hh₀ (mem_univ u) ⟨J,hJI,hb⟩
  · intro J hJI u hu v hv huv
    apply le_of_not_gt
    intro hb
    exact GreedyNonlinearGuards.event_sum_excludes _ _ I hh₁ (b := (u,v))
      (mem_offDiag.mpr ⟨mem_univ u,mem_univ v,huv⟩) ⟨J,hJI,hu,hv,hb⟩
  · intro J hJI u
    apply le_of_not_gt
    intro hb
    exact GreedyNonlinearGuards.event_sum_excludes _ _ I hh₂ (mem_univ u) ⟨J,hJI,hb⟩
  · intro J hJI u
    apply le_of_not_gt
    intro hb
    exact GreedyNonlinearGuards.event_sum_excludes _ _ I hh₃ (mem_univ u) ⟨J,hJI,hb⟩

/-- First hitting of the monotone guard is bounded by its terminal cost,
    regardless of the bookkeeping guard and freezing of its records. -/
theorem auxiliary_hit_le (H : Finset (Finset α)) (C B2 B3 L T : ℕ)
    (G : ℕ → Tracked H T → Prop) :
    hit (GreedyTrackedState.kernel H L T G) (fun _ s => auxiliaryBad H C B2 B3 s.chosen)
      0 T (initial H T) ≤ expectation H L T (cost H C B2 B3) := by
  rw [hit_carrier H L T G _ (fun I J hIJ => auxiliaryBad_mono H C B2 B3 hIJ)]
  apply expectation_mono
  intro I
  classical
  by_cases hb : auxiliaryBad H C B2 B3 I
  · simpa only [event,if_pos hb] using hb
  · simpa only [event,if_neg hb] using cost_nonneg H C B2 B3 I

/-- Uniform concrete first-hit cost in the m^300 codegree regime. -/
theorem auxiliary_tail {H : Finset (Finset α)}
    (h4 : ∀ e ∈ H, e.card = 4)
    (h2 : ∀ e ∈ H, ∀ f ∈ H, e ≠ f → (e ∩ f).card ≤ 2)
    (D K m A : ℕ) (hm : 36 ≤ m) (hAm : A ≤ m)
    (hV : Fintype.card α ≤ m^A) (hD : ∀ u : α, degree H u ≤ D)
    (hK : ∀ a b : α, a ≠ b → pairDegree H a b ≤ K)
    (hDb : D ≤ m^300) (hKb : K ≤ m^3)
    (L T : ℕ) (hL : 0 < L) (hTL : T ≤ L) (hp : (T:ℝ)/L ≤ 1/(m:ℝ)^97)
    (C B2 B3 : ℕ) (hC : 16*K^2*m^15 ≤ C) (hB2 : 288*m^133 ≤ B2) (hB3 : 54*m^274 ≤ B3)
    (G : ℕ → Tracked H T → Prop) :
    hit (GreedyTrackedState.kernel H L T G) (fun _ s => auxiliaryBad H C B2 B3 s.chosen)
      0 T (initial H T) ≤ 8/(m:ℝ)^2 := by
  apply (auxiliary_hit_le H C B2 B3 L T G).trans
  apply le_trans _ (GreedyNonlinearGuards.expectation_badCost h4 h2 D K m A hm hAm hV hD hK hDb hKb L hL T hTL hp)
  exact expectation_mono H L T (fun I => cost_mono (Subset.refl I) hC hB2 hB3)

#print axioms cost_mono
#print axioms controls_of_not_bad
#print axioms auxiliary_hit_le
#print axioms auxiliary_tail
end
end Erdos773.GreedyNonlinearGuardTails
