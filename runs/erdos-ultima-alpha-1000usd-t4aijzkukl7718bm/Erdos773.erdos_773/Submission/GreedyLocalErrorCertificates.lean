import Submission.GreedyLocalDuplicateTails

/-!
Simultaneous all-prefix, all-vertex control of duplicate corrections and residual
common-neighbor counts. The early-stop alternative is explicitly retained.
-/
namespace Erdos773.GreedyLocalErrorCertificates
open Finset GreedyHypergraphState StoppedGreedyMoments GreedyConfigurationTails
open FourUniformRegularization HypergraphDegreeTrim
set_option maxHeartbeats 2500000
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

def badCost (H : Finset (Finset α)) (R : ℕ) (I : Finset α) : ℝ :=
  (∑ u : α, event (GreedyLocalDuplicateTails.prefixBad H u R) I) +
    ∑ uv ∈ (univ : Finset α).offDiag, event (GreedyCommonNeighbors.prefixBad H uv.1 uv.2 R) I

/-- A union bound for the two kinds of all-prefix error. -/
theorem expectation_badCost {H : Finset (Finset α)}
    (h4 : ∀ e ∈ H, e.card = 4)
    (h2 : ∀ e ∈ H, ∀ f ∈ H, e ≠ f → (e ∩ f).card ≤ 2)
    (D K : ℕ) (hD : ∀ v : α, degree H v ≤ D)
    (hK : ∀ a b : α, a ≠ b → pairDegree H a b ≤ K)
    (L : ℕ) (hL : 0 < L) (t : ℕ) (ht : t ≤ L) (k : ℕ) :
    expectation H L t (badCost H (16*K^2*k)) ≤
      (Fintype.card α:ℝ)*(9*D*K*((t:ℝ)/L)^4/(k+1))^(k+1) +
        (Fintype.card α:ℝ)^2*(9*D*K*((t:ℝ)/L)^3/(k+1))^(k+1) := by
  unfold badCost
  rw [expectation_add, expectation_sum, expectation_sum]
  apply add_le_add
  · calc
      _ ≤ ∑ _u : α, (9*D*K*((t:ℝ)/L)^4/(k+1))^(k+1) := by
        apply sum_le_sum
        intro u _
        exact GreedyLocalDuplicateTails.prefix_duplicate_exponential_tail
          h4 h2 u D K (hD u) hK L hL t ht k
      _ = _ := by simp
  · let b : ℝ := (9*D*K*((t:ℝ)/L)^3/(k+1))^(k+1)
    calc
      _ ≤ ∑ _uv ∈ (univ : Finset α).offDiag, b := by
        apply sum_le_sum
        intro uv huv
        have huv := (mem_offDiag.mp huv).2.2
        exact GreedyCommonNeighbors.prefix_common_exponential_tail h4 h2 uv.1 uv.2 huv
          D K (hD uv.1) hK L hL t ht k
      _ = ((univ : Finset α).offDiag.card:ℝ)*b := by simp
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (by dsimp [b]; positivity)
        have hh : (univ : Finset α).offDiag.card ≤ (Fintype.card α)^2 := by
          rw [offDiag_card, card_univ, pow_two]
          exact Nat.sub_le _ _
        exact_mod_cast hh

/-- At least one actual reachable state has both controls at every selected
    subset, and therefore at every prefix of every path realizing that state.
    This theorem does NOT assert that the process reaches t selected vertices. -/
theorem controlled_run {H : Finset (Finset α)}
    (h4 : ∀ e ∈ H, e.card = 4)
    (h2 : ∀ e ∈ H, ∀ f ∈ H, e ≠ f → (e ∩ f).card ≤ 2)
    (D K : ℕ) (hD : ∀ v : α, degree H v ≤ D)
    (hK : ∀ a b : α, a ≠ b → pairDegree H a b ≤ K)
    (L : ℕ) (hL : 0 < L) (t : ℕ) (ht : t ≤ L) (k : ℕ)
    (hprob : (Fintype.card α:ℝ)*(9*D*K*((t:ℝ)/L)^4/(k+1))^(k+1) +
      (Fintype.card α:ℝ)^2*(9*D*K*((t:ℝ)/L)^3/(k+1))^(k+1) < 1) :
    ∃ I : Finset α, Reach H L t I ∧ Independent H I ∧
      (I.card = t ∨ (available H I).card < L) ∧
      (∀ J ⊆ I, ∀ u : α, duplicateExcess H J u ≤ 16*K^2*k) ∧
      ∀ J ⊆ I, ∀ u ∈ available H J, ∀ v ∈ available H J, u ≠ v →
        GreedyCommonNeighbors.commonDegree H J u v ≤ 16*K^2*k := by
  classical
  obtain ⟨I,hI,hcost⟩ := expectation_attained_below H L t (badCost H (16*K^2*k))
  have hsmall : badCost H (16*K^2*k) I < 1 := hcost.trans_lt
    ((expectation_badCost h4 h2 D K hD hK L hL t ht k).trans_lt hprob)
  have hn : ∀ e ∈ H, e.Nonempty := fun e he => card_pos.mp (by rw [h4 e he]; decide)
  refine ⟨I,hI,hI.independent hn,hI.card_or_stopped hL,?_,?_⟩
  · intro J hJI u
    by_contra! hb
    have hp : GreedyLocalDuplicateTails.prefixBad H u (16*K^2*k) I := ⟨J,hJI,hb⟩
    have hh : event (GreedyLocalDuplicateTails.prefixBad H u (16*K^2*k)) I = 1 := by
      simp only [event,if_pos hp]
    have hs := single_le_sum (s := (univ : Finset α)) (a := u)
      (f := fun u => event (GreedyLocalDuplicateTails.prefixBad H u (16*K^2*k)) I)
      (fun _ _ => event_nonneg _ _) (mem_univ u)
    dsimp only at hs
    rw [hh] at hs
    have hn : 0 ≤ ∑ uv ∈ (univ : Finset α).offDiag,
        event (GreedyCommonNeighbors.prefixBad H uv.1 uv.2 (16*K^2*k)) I :=
      sum_nonneg (fun _ _ => event_nonneg _ _)
    unfold badCost at hsmall
    linarith only [hsmall,hs,hn]
  · intro J hJI u hu v hv huv
    by_contra! hb
    have hp : GreedyCommonNeighbors.prefixBad H u v (16*K^2*k) I := ⟨J,hJI,hu,hv,hb⟩
    have hh : event (GreedyCommonNeighbors.prefixBad H u v (16*K^2*k)) I = 1 := by
      simp only [event, if_pos hp]
    have hs := single_le_sum (s := (univ : Finset α).offDiag) (a := (u,v))
      (f := fun uv => event (GreedyCommonNeighbors.prefixBad H uv.1 uv.2 (16*K^2*k)) I)
      (fun uv _ => event_nonneg _ _) (mem_offDiag.mpr ⟨mem_univ u,mem_univ v,huv⟩)
    change event (GreedyCommonNeighbors.prefixBad H u v (16*K^2*k)) I ≤ _ at hs
    dsimp only at hs
    rw [hh] at hs
    have hn : 0 ≤ ∑ u : α, event (GreedyLocalDuplicateTails.prefixBad H u (16*K^2*k)) I :=
      sum_nonneg (fun _ _ => event_nonneg _ _)
    unfold badCost at hsmall
    linarith

#print axioms expectation_badCost
#print axioms controlled_run
end
end Erdos773.GreedyLocalErrorCertificates
