import Submission.GreedyHigherPromotionScales
import Submission.GreedyLocalErrorCertificates

/-!
All-prefix nonlinear guard certificates: common neighbors, local duplicate
corrections, and both promotion deficits. The early-stop alternative remains.
-/
namespace Erdos773.GreedyNonlinearGuards
open Finset GreedyHypergraphState GreedyCodegreeDrift
open GreedyConfigurationTails StoppedGreedyMoments FourUniformRegularization HypergraphDegreeTrim
set_option maxHeartbeats 2500000
set_option exponentiation.threshold 1024
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

def badCost (H : Finset (Finset α)) (K m : ℕ) (I : Finset α) : ℝ :=
  GreedyLocalErrorCertificates.badCost H (16*K^2*m^15) I +
  (∑ u : α, event (GreedyPromotionTails.prefixBad H u (288*m^133)) I) +
  (∑ u : α, event (GreedyHigherPromotionTails.prefixBad H u (54*m^274)) I)

lemma local_error_bound {H : Finset (Finset α)}
    (h4 : ∀ e ∈ H, e.card = 4)
    (h2 : ∀ e ∈ H, ∀ f ∈ H, e ≠ f → (e ∩ f).card ≤ 2)
    (D K m A : ℕ) (hm : 36 ≤ m) (hAm : A ≤ m)
    (hV : Fintype.card α ≤ m^A) (hD : ∀ u : α, degree H u ≤ D)
    (hK : ∀ a b : α, a ≠ b → pairDegree H a b ≤ K)
    (hDb : D ≤ m^300) (hKb : K ≤ m^3)
    (L : ℕ) (hL : 0 < L) (n : ℕ) (hn : n ≤ L) (hp : (n:ℝ)/L ≤ 1/(m:ℝ)^97) :
    expectation H L n (GreedyLocalErrorCertificates.badCost H (16*K^2*m^15)) ≤ 2/(m:ℝ)^2 := by
  have hmR : (36:ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0:ℝ) < m := by linarith only [hmR]
  have hDbR : (D:ℝ) ≤ (m:ℝ)^300 := by exact_mod_cast hDb
  have hKbR : (K:ℝ) ≤ (m:ℝ)^3 := by exact_mod_cast hKb
  have hp0 : (0:ℝ) ≤ (n:ℝ)/L := by positivity
  have hp1 : (n:ℝ)/L ≤ 1 := by
    apply (div_le_one (by exact_mod_cast hL : (0:ℝ) < L)).mpr
    exact_mod_cast hn
  have hb : 9*(D:ℝ)*K*((n:ℝ)/L)^3/((m:ℝ)^15+1) ≤ 1/(m:ℝ)^2 := by
    apply le_trans _ (GreedyPromotionScales.ratio_three hmR (Nat.cast_nonneg D)
      (Nat.cast_nonneg K) hp0 hDbR hKbR hp)
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hx : 0 ≤ (D:ℝ)*K*((n:ℝ)/L)^3 := by positivity
    nlinarith only [hx]
  have hb4 : 9*(D:ℝ)*K*((n:ℝ)/L)^4/((m:ℝ)^15+1) ≤ 1/(m:ℝ)^2 := by
    apply le_trans _ hb
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hp0 hp1 (by omega : 3 ≤ 4)) (by positivity)
  have hpow3 := pow_le_pow_left₀ (by positivity) hb (m^15+1)
  have hpow4 := pow_le_pow_left₀ (by positivity) hb4 (m^15+1)
  have hc := GreedyLocalErrorCertificates.expectation_badCost h4 h2 D K hD hK L hL n hn (m^15)
  push_cast at hc
  apply hc.trans
  have hh := add_le_add
    (mul_le_mul_of_nonneg_left hpow4 (Nat.cast_nonneg (Fintype.card α)))
    (mul_le_mul_of_nonneg_left hpow3 (sq_nonneg (Fintype.card α:ℝ)))
  have hv := GreedyPromotionScales.volume_power_bound m A hm hAm
    (Nat.cast_nonneg (Fintype.card α)) (by exact_mod_cast hV)
  nlinarith only [hh,hv]

/-- A concrete total guard-failure cost, valid for the nonlinear original
    hypergraph and uniform over all selected prefixes. -/
theorem expectation_badCost {H : Finset (Finset α)}
    (h4 : ∀ e ∈ H, e.card = 4)
    (h2 : ∀ e ∈ H, ∀ f ∈ H, e ≠ f → (e ∩ f).card ≤ 2)
    (D K m A : ℕ) (hm : 36 ≤ m) (hAm : A ≤ m)
    (hV : Fintype.card α ≤ m^A) (hD : ∀ u : α, degree H u ≤ D)
    (hK : ∀ a b : α, a ≠ b → pairDegree H a b ≤ K)
    (hDb : D ≤ m^300) (hKb : K ≤ m^3)
    (L : ℕ) (hL : 0 < L) (n : ℕ) (hn : n ≤ L) (hp : (n:ℝ)/L ≤ 1/(m:ℝ)^97) :
    expectation H L n (badCost H K m) ≤ 8/(m:ℝ)^2 := by
  unfold badCost
  rw [expectation_add,expectation_add]
  have h₀ := local_error_bound h4 h2 D K m A hm hAm hV hD hK hDb hKb L hL n hn hp
  have h₁ := GreedyPromotionScales.all_vertex_polynomial_tail h4 h2 D K m A hm hAm hV hD hK hDb hKb L hL n hn hp
  have h₂ := GreedyHigherPromotionScales.all_vertex_polynomial_tail h4 h2 D K m A hm hAm hV hD hK hDb hKb L hL n hn hp
  apply (add_le_add (add_le_add h₀ h₁) h₂).trans_eq
  ring

omit [Fintype α] [DecidableEq α] in
lemma event_sum_excludes {β γ : Type*} (S : Finset β) (P : β → Finset γ → Prop)
    (I : Finset γ) (hsmall : (∑ b ∈ S, event (P b) I) < 1) {b : β} (hb : b ∈ S) : ¬P b I := by
  classical
  intro hbad
  have hs := single_le_sum (s := S) (a := b) (f := fun b => event (P b) I)
    (fun _ _ => event_nonneg _ _) hb
  dsimp only at hs
  have he : event (P b) I = 1 := by simp only [event,if_pos hbad]
  rw [he] at hs
  linarith only [hsmall,hs]

/-- An actual reachable independent state satisfies every nonlinear error
    guard at every selected subset. Its early-stop alternative is explicit. -/
theorem controlled_run {H : Finset (Finset α)}
    (h4 : ∀ e ∈ H, e.card = 4)
    (h2 : ∀ e ∈ H, ∀ f ∈ H, e ≠ f → (e ∩ f).card ≤ 2)
    (D K m A : ℕ) (hm : 36 ≤ m) (hAm : A ≤ m)
    (hV : Fintype.card α ≤ m^A) (hD : ∀ u : α, degree H u ≤ D)
    (hK : ∀ a b : α, a ≠ b → pairDegree H a b ≤ K)
    (hDb : D ≤ m^300) (hKb : K ≤ m^3)
    (L : ℕ) (hL : 0 < L) (n : ℕ) (hn : n ≤ L) (hp : (n:ℝ)/L ≤ 1/(m:ℝ)^97) :
    ∃ I : Finset α, Reach H L n I ∧ Independent H I ∧
      (I.card = n ∨ (available H I).card < L) ∧
      (∀ J ⊆ I, ∀ u : α, duplicateExcess H J u ≤ 16*m^21) ∧
      (∀ J ⊆ I, ∀ u ∈ available H J, ∀ v ∈ available H J, u ≠ v →
        GreedyCommonNeighbors.commonDegree H J u v ≤ 16*m^21) ∧
      (∀ J ⊆ I, ∀ u : α, promotionDefect H J 2 u ≤ 288*m^133) ∧
      (∀ J ⊆ I, ∀ u : α, promotionDefect H J 3 u ≤ 54*m^274) := by
  classical
  obtain ⟨I,hI,hi⟩ := expectation_attained_below H L n (badCost H K m)
  have hmR : (36:ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0:ℝ) < m := by linarith only [hmR]
  have hsmall : badCost H K m I < 1 := by
    apply hi.trans_lt ((expectation_badCost h4 h2 D K m A hm hAm hV hD hK hDb hKb L hL n hn hp).trans_lt _)
    apply (div_lt_one (sq_pos_of_pos hm0)).mpr
    nlinarith only [hmR]
  have hn₀ : 0 ≤ ∑ u : α, event (GreedyLocalDuplicateTails.prefixBad H u (16*K^2*m^15)) I :=
    sum_nonneg (fun _ _ => event_nonneg _ _)
  have hn₁ : 0 ≤ ∑ uv ∈ (univ : Finset α).offDiag,
      event (GreedyCommonNeighbors.prefixBad H uv.1 uv.2 (16*K^2*m^15)) I :=
    sum_nonneg (fun _ _ => event_nonneg _ _)
  have hn₂ : 0 ≤ ∑ u : α, event (GreedyPromotionTails.prefixBad H u (288*m^133)) I :=
    sum_nonneg (fun _ _ => event_nonneg _ _)
  have hn₃ : 0 ≤ ∑ u : α, event (GreedyHigherPromotionTails.prefixBad H u (54*m^274)) I :=
    sum_nonneg (fun _ _ => event_nonneg _ _)
  unfold badCost GreedyLocalErrorCertificates.badCost at hsmall
  have h₀ : (∑ u : α, event (GreedyLocalDuplicateTails.prefixBad H u (16*K^2*m^15)) I) < 1 := by linarith
  have h₁ : (∑ uv ∈ (univ : Finset α).offDiag,
      event (GreedyCommonNeighbors.prefixBad H uv.1 uv.2 (16*K^2*m^15)) I) < 1 := by linarith
  have h₂ : (∑ u : α, event (GreedyPromotionTails.prefixBad H u (288*m^133)) I) < 1 := by linarith
  have h₃ : (∑ u : α, event (GreedyHigherPromotionTails.prefixBad H u (54*m^274)) I) < 1 := by linarith
  have hR : 16*K^2*m^15 ≤ 16*m^21 := by
    calc
      _ ≤ 16*(m^3)^2*m^15 := by gcongr
      _ = _ := by ring
  have he : ∀ e ∈ H, e.Nonempty := fun e he => card_pos.mp (by rw [h4 e he]; decide)
  refine ⟨I,hI,hI.independent he,hI.card_or_stopped hL,?_,?_,?_,?_⟩
  · intro J hJI u
    apply le_trans _ hR
    apply le_of_not_gt
    intro hb
    exact event_sum_excludes _ _ I h₀ (mem_univ u) ⟨J,hJI,hb⟩
  · intro J hJI u hu v hv huv
    apply le_trans _ hR
    apply le_of_not_gt
    intro hb
    exact event_sum_excludes _ _ I h₁ (b := (u,v)) (mem_offDiag.mpr ⟨mem_univ u,mem_univ v,huv⟩)
      ⟨J,hJI,hu,hv,hb⟩
  · intro J hJI u
    apply le_of_not_gt
    intro hb
    exact event_sum_excludes _ _ I h₂ (mem_univ u) ⟨J,hJI,hb⟩
  · intro J hJI u
    apply le_of_not_gt
    intro hb
    exact event_sum_excludes _ _ I h₃ (mem_univ u) ⟨J,hJI,hb⟩

#print axioms local_error_bound
#print axioms expectation_badCost
#print axioms controlled_run
end
end Erdos773.GreedyNonlinearGuards
