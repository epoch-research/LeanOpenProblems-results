import Submission.GreedyProfileVariance
import Submission.GreedyCodegreeVariance
import Submission.GreedyRecordedCrossing

/-!
Nonlinear deterministic variance and increment caps from uniform degree caps. These
supply actual MomentControl instances, including unavailable vertices.
-/
namespace Erdos773.GreedyCodegreeMomentControl
open Finset GreedyHypergraphState StoppedGreedyMoments
open GreedyLinearDrift GreedyLinearLocal GreedyCommonNeighbors
open GreedyCodegreeVariance GreedyProfileDrift GreedyTrackedState GreedyRecordedCrossing
open FourUniformRegularization
set_option maxHeartbeats 2500000
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

lemma raw_two_increment {H : Finset (Finset α)} (K : ℕ)
    (hK : ∀ a b : α, a ≠ b → pairDegree H a b ≤ K)
    (I : Finset α) (u : α) (C E : ℕ)
    (hC : ∀ x ∈ available H I, ∀ y ∈ available H I, x ≠ y → commonDegree H I x y ≤ C)
    (hE : ∀ x ∈ available H I, duplicateExcess H I x ≤ E)
    (w : α) (hw : w ∈ safeChoices H I u) :
    |((incident H (insert w I) 2 u).card:ℝ)-(incident H I 2 u).card| ≤ (K:ℝ)+C+E := by
  obtain ⟨hw,hu⟩ := mem_filter.mp hw
  have hu0 := available_antitone (subset_insert w I) hu
  have huw : u ≠ w := by intro hh; exact (mem_available.mp hu).1 (by simp [hh])
  exact GreedyCodegreeLocal.incident_two_increment_bound K hK hw hu C E (hC u hu0 w hw huw) (hE u hu0)

lemma raw_higher_increment {H : Finset (Finset α)} (K : ℕ)
    (hK : ∀ a b : α, a ≠ b → pairDegree H a b ≤ K)
    (I : Finset α) (j : ℕ) (u : α) (U2 : ℝ)
    (h2 : ∀ x ∈ available H I, ((incident H I 2 x).card:ℝ) ≤ U2)
    (w : α) (hw : w ∈ safeChoices H I u) :
    |((incident H (insert w I) j u).card:ℝ)-(incident H I j u).card| ≤ (K:ℝ)*(U2+1) := by
  obtain ⟨hw,hu⟩ := mem_filter.mp hw
  have hh := GreedyCodegreeLocal.incident_increment_bound K hK hw hu j
  have hc : ((closes H I w).card:ℝ) ≤ (incident H I 2 w).card := by
    exact_mod_cast closes_card_le_incident hw
  exact hh.trans (mul_le_mul_of_nonneg_left (add_le_add (hc.trans (h2 w hw)) le_rfl) (by positivity))

/-- A deterministic raw second-moment numerator, valid even for dead u. -/
theorem raw_two_variance {H : Finset (Finset α)} (K : ℕ)
    (hK : ∀ a b : α, a ≠ b → pairDegree H a b ≤ K)
    (I : Finset α) (u : α) (U2 U3 : ℝ) (hU2 : 0 ≤ U2) (hU3 : 0 ≤ U3) (C E : ℕ)
    (h2 : ∀ x ∈ available H I, ((incident H I 2 x).card:ℝ) ≤ U2)
    (h3 : u ∈ available H I → ((incident H I 3 u).card:ℝ) ≤ U3)
    (hC : ∀ x ∈ available H I, ∀ y ∈ available H I, x ≠ y → commonDegree H I x y ≤ C)
    (hE : ∀ x ∈ available H I, duplicateExcess H I x ≤ E) :
    (∑ w ∈ safeChoices H I u,
      (((incident H (insert w I) 2 u).card:ℝ)-(incident H I 2 u).card)^2) ≤
        ((K:ℝ)+C+E)*(2*U3+U2^2) := by
  by_cases hu : u ∈ available H I
  · have hh := local_two_second_moment K hK hu U2 C E
      (fun x hx => h2 x (closes_subset H I u hx)) (hC u hu) (hE u hu)
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hmul := mul_le_mul_of_nonneg_left (h2 u hu) hU2
    nlinarith only [h3 hu,hmul]
  · rw [safeChoices_eq_empty_of_unavailable hu,sum_empty]
    positivity

/-- Deterministic raw variance numerator for residual sizes at least three. -/
theorem raw_higher_variance {H : Finset (Finset α)} (K : ℕ)
    (hK : ∀ a b : α, a ≠ b → pairDegree H a b ≤ K)
    (I : Finset α) (j : ℕ) (hj : 3 ≤ j) (u : α) (U2 Uj Un : ℝ) (hU2 : 0 ≤ U2)
    (h2 : ∀ x ∈ available H I, ((incident H I 2 x).card:ℝ) ≤ U2)
    (hl : ((incident H I j u).card:ℝ) ≤ Uj)
    (hn : ((incident H I (j+1) u).card:ℝ) ≤ Un) :
    (∑ w ∈ safeChoices H I u,
      (((incident H (insert w I) j u).card:ℝ)-(incident H I j u).card)^2) ≤
        (K:ℝ)*(U2+1)*((j:ℝ)*Un+(j-1:ℕ)*(U2+1)*Uj) := by
  apply (local_higher_second_moment K hK I j hj u U2 hU2 h2).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact add_le_add (mul_le_mul_of_nonneg_left hn (by positivity))
    (mul_le_mul_of_nonneg_left hl (by positivity))

/-- Recorded two-degree MomentControl with an explicit variance function.
    The uniform degree, common-neighbor and Q caps are guard obligations. -/
theorem two_moment_control {H : Finset (Finset α)} (K : ℕ)
    (hK : ∀ a b : α, a ≠ b → pairDegree H a b ≤ K)
    (L T : ℕ) (G : ℕ → Tracked H T → Prop) (f : ℕ → ℝ) (u : α)
    (sign b : ℝ) (hsign : |sign| = 1) (U2 U3 qmin : ℕ → ℝ) (C E : ℕ → ℕ)
    (hU2 : ∀ n < T, 0 ≤ U2 n) (hU3 : ∀ n < T, 0 ≤ U3 n)
    (hq : ∀ n < T, 0 < qmin n)
    (hcap : ∀ n < T, ((K:ℝ)+C n+E n)+|f (n+1)-f n| ≤ b)
    (hvalid : ∀ n < T, ∀ s, G n s → Valid H L n s)
    (hQ : ∀ n < T, ∀ s, G n s → qmin n ≤ ((available H s.chosen).card:ℝ))
    (h2 : ∀ n < T, ∀ s, G n s → ∀ x ∈ available H s.chosen,
      ((incident H s.chosen 2 x).card:ℝ) ≤ U2 n)
    (h3 : ∀ n < T, ∀ s, G n s → u ∈ available H s.chosen →
      ((incident H s.chosen 3 u).card:ℝ) ≤ U3 n)
    (hC : ∀ n < T, ∀ s, G n s → ∀ x ∈ available H s.chosen, ∀ y ∈ available H s.chosen,
      x ≠ y → commonDegree H s.chosen x y ≤ C n)
    (hE : ∀ n < T, ∀ s, G n s → ∀ x ∈ available H s.chosen, duplicateExcess H s.chosen x ≤ E n) :
    MomentControl H L T G f 0 u sign b (fun n => (K:ℝ)+C n+E n)
      (fun n => 2*(((K:ℝ)+C n+E n)*(2*U3 n+(U2 n)^2)/qmin n)+2*(f (n+1)-f n)^2) := by
  refine ⟨hsign,hvalid,fun n hn => by positivity,?_,hcap,?_,?_⟩
  · intro n hn
    have h3 := hU3 n hn
    have hp := hq n hn
    positivity
  · intro n hn s hr hrun hg w hw
    exact raw_two_increment K hK s.chosen u (C n) (E n) (hC n hn s hg) (hE n hn s hg) w hw
  · intro n hn s hr hrun hg
    have hv := raw_two_variance K hK s.chosen u (U2 n) (U3 n) (hU2 n hn) (hU3 n hn)
      (C n) (E n) (h2 n hn s hg) (h3 n hn s hg) (hC n hn s hg) (hE n hn s hg)
    apply GreedyProfileVariance.divide_variance _ _ _ _ _ hv _ (hq n hn) (hQ n hn s hg)
    have h3 := hU3 n hn
    positivity

/-- Higher-degree MomentControl with deterministic promotion/loss variance.
    A size-four original hypergraph may take Un=0 for its tracked d_4. -/
theorem higher_moment_control {H : Finset (Finset α)} (K : ℕ)
    (hK : ∀ a b : α, a ≠ b → pairDegree H a b ≤ K)
    (L T : ℕ) (G : ℕ → Tracked H T → Prop) (f : ℕ → ℝ) (j : Fin 3) (hj : 1 ≤ j.val) (u : α)
    (sign b : ℝ) (hsign : |sign| = 1) (U2 Uj Un qmin : ℕ → ℝ)
    (hU2 : ∀ n < T, 0 ≤ U2 n) (hUj : ∀ n < T, 0 ≤ Uj n) (hUn : ∀ n < T, 0 ≤ Un n)
    (hq : ∀ n < T, 0 < qmin n)
    (hcap : ∀ n < T, (K:ℝ)*(U2 n+1)+|f (n+1)-f n| ≤ b)
    (hvalid : ∀ n < T, ∀ s, G n s → Valid H L n s)
    (hQ : ∀ n < T, ∀ s, G n s → qmin n ≤ ((available H s.chosen).card:ℝ))
    (h2 : ∀ n < T, ∀ s, G n s → ∀ x ∈ available H s.chosen,
      ((incident H s.chosen 2 x).card:ℝ) ≤ U2 n)
    (hl : ∀ n < T, ∀ s, G n s → ((incident H s.chosen (j.val+2) u).card:ℝ) ≤ Uj n)
    (hnxt : ∀ n < T, ∀ s, G n s → ((incident H s.chosen (j.val+3) u).card:ℝ) ≤ Un n) :
    MomentControl H L T G f j u sign b (fun n => (K:ℝ)*(U2 n+1))
      (fun n => 2*((K:ℝ)*(U2 n+1)*((j.val+2:ℕ)*Un n+(j.val+1:ℕ)*(U2 n+1)*Uj n)/qmin n)+
        2*(f (n+1)-f n)^2) := by
  refine ⟨hsign,hvalid,?_,?_,hcap,?_,?_⟩
  · intro n hn
    have h2 := hU2 n hn
    positivity
  · intro n hn
    have h2 := hU2 n hn
    have hj := hUj n hn
    have hnext := hUn n hn
    have hp := hq n hn
    positivity
  · intro n hn s hr hrun hg w hw
    exact raw_higher_increment K hK s.chosen (j.val+2) u (U2 n) (h2 n hn s hg) w hw
  · intro n hn s hr hrun hg
    have hv := raw_higher_variance K hK s.chosen (j.val+2) (by omega) u (U2 n) (Uj n) (Un n)
      (hU2 n hn) (h2 n hn s hg) (hl n hn s hg) (hnxt n hn s hg)
    have hnon : 0 ≤ (K:ℝ)*(U2 n+1)*((j.val+2:ℕ)*Un n+(j.val+1:ℕ)*(U2 n+1)*Uj n) := by
      have h2 := hU2 n hn
      have hj := hUj n hn
      have hnext := hUn n hn
      positivity
    convert GreedyProfileVariance.divide_variance _ _ _ _ _ hv hnon (hq n hn) (hQ n hn s hg) using 1

#print axioms raw_two_variance
#print axioms raw_higher_variance
#print axioms two_moment_control
#print axioms higher_moment_control
end
end Erdos773.GreedyCodegreeMomentControl
