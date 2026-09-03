import Submission.GreedyHigherPromotionWitnesses
import Submission.GreedyTwoWitnessTails

/-! Heavy/light all-prefix bounds for failed four-to-three promotions. -/
namespace Erdos773.GreedyHigherPromotionTails
open Finset GreedyHypergraphState GreedyCodegreeDrift GreedyHigherPromotionWitnesses
open GreedyConfigurationTails StoppedGreedyMoments FourUniformRegularization HypergraphDegreeTrim
set_option maxHeartbeats 2500000
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

def prefixBad (H : Finset (Finset α)) (u : α) (B : ℕ) (I : Finset α) : Prop :=
  ∃ J ⊆ I, B < promotionDefect H J 3 u

theorem prefix_promotion_tail {H : Finset (Finset α)}
    (h4 : ∀ e ∈ H, e.card = 4)
    (h2 : ∀ e ∈ H, ∀ f ∈ H, e ≠ f → (e ∩ f).card ≤ 2)
    (u : α) (D K : ℕ) (hD : degree H u ≤ D)
    (hK : ∀ a b : α, a ≠ b → pairDegree H a b ≤ K)
    (L : ℕ) (hL : 0 < L) (n : ℕ) (hn : n ≤ L) (h l₀ l₁ s k : ℕ) (hh : 0 < h) :
    expectation H L n (event (prefixBad H u (18*K^2*l₀*s+36*K^2*l₁*k))) ≤
      (Fintype.card α:ℝ)*(18*D*K*((n:ℝ)/L)/(l₀+1))^(l₀+1) +
      (Fintype.card α:ℝ)*(3*h*((n:ℝ)/L)/(l₁+1))^(l₁+1) +
      (36*D*K*((n:ℝ)/L)/(h*(s+1)))^(s+1) +
      (18*D*K*((n:ℝ)/L)^2/(k+1))^(k+1) := by
  have hdom (I : Finset α) : event (prefixBad H u (18*K^2*l₀*s+36*K^2*l₁*k)) I ≤
      event (fun I => s*((6*K^2)*l₀)+2*((6*K^2)*l₁)*k < cost H u I) I := by
    classical
    by_cases hb : prefixBad H u (18*K^2*l₀*s+36*K^2*l₁*k) I
    · have hlt : s*((6*K^2)*l₀)+2*((6*K^2)*l₁)*k < cost H u I := by
        obtain ⟨J,hJI,hb⟩ := hb
        have ht := (promotionDefect_bound H J u 3 (by omega)).trans
          (Nat.mul_le_mul_left 3 (cost_mono H u hJI))
        nlinarith only [ht,hb]
      simp only [event,if_pos hb,if_pos hlt,le_refl]
    · simpa only [event,if_neg hb] using event_nonneg
        (fun I => s*((6*K^2)*l₀)+2*((6*K^2)*l₁)*k < cost H u I) I
  have ht := GreedyTwoWitnessTails.two_tail H L hL n hn (patterns H u) witness
    (fun ef hef => witness_card h4 h2 hef) (6*D*K) h (6*K^2) l₀ l₁ s k
    (patterns_card_le h4 u D K hD hK) hh
    (fun a b hab => witness_pair_incidence h4 u a b hab K hK)
  apply (expectation_mono H L n hdom).trans
  convert ht using 1; push_cast; ring

theorem prefix_promotion_tail_of_le {H : Finset (Finset α)}
    (h4 : ∀ e ∈ H, e.card = 4)
    (h2 : ∀ e ∈ H, ∀ f ∈ H, e ≠ f → (e ∩ f).card ≤ 2)
    (u : α) (D K : ℕ) (hD : degree H u ≤ D)
    (hK : ∀ a b : α, a ≠ b → pairDegree H a b ≤ K)
    (L : ℕ) (hL : 0 < L) (n : ℕ) (hn : n ≤ L) (h l₀ l₁ s k B : ℕ) (hh : 0 < h)
    (hB : 18*K^2*l₀*s+36*K^2*l₁*k ≤ B) :
    expectation H L n (event (prefixBad H u B)) ≤
      (Fintype.card α:ℝ)*(18*D*K*((n:ℝ)/L)/(l₀+1))^(l₀+1) +
      (Fintype.card α:ℝ)*(3*h*((n:ℝ)/L)/(l₁+1))^(l₁+1) +
      (36*D*K*((n:ℝ)/L)/(h*(s+1)))^(s+1) +
      (18*D*K*((n:ℝ)/L)^2/(k+1))^(k+1) := by
  have hm (I : Finset α) : event (prefixBad H u B) I ≤
      event (prefixBad H u (18*K^2*l₀*s+36*K^2*l₁*k)) I := by
    classical
    by_cases hb : prefixBad H u B I
    · have hb' : prefixBad H u (18*K^2*l₀*s+36*K^2*l₁*k) I := by
        obtain ⟨J,hJI,hJ⟩ := hb
        exact ⟨J,hJI,hB.trans_lt hJ⟩
      simp only [event,if_pos hb,if_pos hb',le_refl]
    · simpa only [event,if_neg hb] using event_nonneg _ I
  exact (expectation_mono H L n hm).trans
    (prefix_promotion_tail h4 h2 u D K hD hK L hL n hn h l₀ l₁ s k hh)

#print axioms prefix_promotion_tail
#print axioms prefix_promotion_tail_of_le
end
end Erdos773.GreedyHigherPromotionTails
