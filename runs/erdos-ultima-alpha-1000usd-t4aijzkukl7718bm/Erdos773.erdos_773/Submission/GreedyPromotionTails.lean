import Submission.GreedyPromotionWitnesses
import Submission.GreedyTripleWitnessTails

/-! All-prefix tail bounds for failed promotions to residual size two. -/
namespace Erdos773.GreedyPromotionTails
open Finset GreedyHypergraphState GreedyCodegreeDrift GreedyPromotionWitnesses
open GreedyConfigurationTails StoppedGreedyMoments FourUniformRegularization HypergraphDegreeTrim
set_option maxHeartbeats 2500000
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

def prefixBad (H : Finset (Finset α)) (u : α) (B : ℕ) (I : Finset α) : Prop :=
  ∃ J ⊆ I, B < promotionDefect H J 2 u

/-- A stopped-process bound controlling the promotion deficit at all selected
    subsets, and hence every prefix. Original edges need not be linear. -/
theorem prefix_promotion_tail {H : Finset (Finset α)}
    (h4 : ∀ e ∈ H, e.card = 4)
    (h2 : ∀ e ∈ H, ∀ f ∈ H, e ≠ f → (e ∩ f).card ≤ 2)
    (u : α) (D K : ℕ) (hD : degree H u ≤ D)
    (hK : ∀ a b : α, a ≠ b → pairDegree H a b ≤ K)
    (L : ℕ) (hL : 0 < L) (n : ℕ) (hn : n ≤ L) (l k : ℕ) :
    expectation H L n (event (prefixBad H u (288*K^2*l*k))) ≤
      (Fintype.card α:ℝ)*(36*D*K*((n:ℝ)/L)^2/(l+1))^(l+1) +
      (36*D*K*((n:ℝ)/L)^3/(k+1))^(k+1) := by
  have hdom (I : Finset α) : event (prefixBad H u (288*K^2*l*k)) I ≤
      event (fun I => 6*(24*K^2)*l*k < cost H u I) I := by
    classical
    by_cases hb : prefixBad H u (288*K^2*l*k) I
    · have hlt : 6*(24*K^2)*l*k < cost H u I := by
        obtain ⟨J,hJI,hb⟩ := hb
        have hh := (promotionDefect_two_bound h4 h2 J u).trans
          (Nat.mul_le_mul_left 2 (cost_mono H u hJI))
        nlinarith only [hh,hb]
      simp only [event,if_pos hb,if_pos hlt,le_refl]
    · simpa only [event,if_neg hb] using event_nonneg
        (fun I => 6*(24*K^2)*l*k < cost H u I) I
  have ht := GreedyTripleWitnessTails.triple_exponential_tail H L hL n hn
    (patterns H u) witness (fun x hx => witness_card h4 h2 hx) (24*K^2) l k
    (fun a b hab => witness_pair_incidence h4 h2 u a b hab K hK)
  apply (expectation_mono H L n hdom).trans (ht.trans _)
  have hc : ((patterns H u).card:ℝ) ≤ 12*(D:ℝ)*K := by
    exact_mod_cast patterns_card_le h4 h2 u D K hD hK
  have hb (s q : ℕ) :
      (3*(patterns H u).card*((n:ℝ)/L)^s/(q+1))^(q+1) ≤
        (36*D*K*((n:ℝ)/L)^s/(q+1))^(q+1) := by
    apply pow_le_pow_left₀ (by positivity)
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hh := mul_le_mul_of_nonneg_right hc (show 0 ≤ 3*((n:ℝ)/L)^s by positivity)
    nlinarith only [hh]
  exact add_le_add (mul_le_mul_of_nonneg_left (hb 2 l) (Nat.cast_nonneg _)) (hb 3 k)

/-- The same bound for any larger proposed threshold. -/
theorem prefix_promotion_tail_of_le {H : Finset (Finset α)}
    (h4 : ∀ e ∈ H, e.card = 4)
    (h2 : ∀ e ∈ H, ∀ f ∈ H, e ≠ f → (e ∩ f).card ≤ 2)
    (u : α) (D K : ℕ) (hD : degree H u ≤ D)
    (hK : ∀ a b : α, a ≠ b → pairDegree H a b ≤ K)
    (L : ℕ) (hL : 0 < L) (n : ℕ) (hn : n ≤ L) (l k B : ℕ)
    (hB : 288*K^2*l*k ≤ B) :
    expectation H L n (event (prefixBad H u B)) ≤
      (Fintype.card α:ℝ)*(36*D*K*((n:ℝ)/L)^2/(l+1))^(l+1) +
      (36*D*K*((n:ℝ)/L)^3/(k+1))^(k+1) := by
  have hm (I : Finset α) : event (prefixBad H u B) I ≤ event (prefixBad H u (288*K^2*l*k)) I := by
    classical
    by_cases hb : prefixBad H u B I
    · have hb' : prefixBad H u (288*K^2*l*k) I := by
        obtain ⟨J,hJI,hJ⟩ := hb
        exact ⟨J,hJI,hB.trans_lt hJ⟩
      simp only [event,if_pos hb,if_pos hb',le_refl]
    · simpa only [event,if_neg hb] using event_nonneg _ I
  exact (expectation_mono H L n hm).trans
    (prefix_promotion_tail h4 h2 u D K hD hK L hL n hn l k)

#print axioms prefix_promotion_tail
#print axioms prefix_promotion_tail_of_le
end
end Erdos773.GreedyPromotionTails
