import Submission.GreedyBatchCommonBudgets
import Submission.GreedyBatchCommonStep
import Submission.BernoulliEvents

/-! Common-neighbor upper tails for the actual conservative next-system,
with explicit mixed degree and shared-link witness budgets. -/
namespace Erdos773.GreedyBatchCommonTail
open Finset HypergraphDegreeTrim UniformLayerRegularization GreedyBatchState
open RegularizationCommonNeighbors GreedyMixedCommonTails GreedyBatchCommonBudgets BernoulliEvents
open FourUniformRegularization (pairDegree)
set_option maxHeartbeats 3000000
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem common_tail (H : Finset (Finset α)) (x y : α) (hxy : x≠y) (D2 D3 D4 P B C q : ℕ)
    (hH : ∀ e∈H, 2≤e.card ∧ e.card≤4)
    (hI : ∀ e∈H, ∀ f∈H, e≠f → (e∩f).card≤2)
    (hP : ∀ a b, a≠b → pairDegree H a b≤P)
    (h2 : ∀ a, degree (layer H 2) a≤D2) (h3 : ∀ a, degree (layer H 3) a≤D3)
    (h4 : ∀ a, degree (layer H 4) a≤D4)
    (hB : RegularizationSharedLinks.count H x y≤B) (hC : common H x y≤C)
    (p : ℝ) (L : ℕ → ℝ) (hp : 0≤p) (hp1 : p≤1) (hL : ∀ r∈Icc 1 4, 0<L r) :
    prob p (fun R => (C:ℝ)+(∑ r∈Icc 1 4, L r)<(common (next H R) x y:ℝ)) ≤
      ∑ r∈Icc 1 4, (IndexedBernoulliMoments.budget r q
        (overlapCaps (masses D2 D3 D4 P B r) P) p/L r)^q := by
  have hcover (R : Finset α) (hbad : (C:ℝ)+(∑ r∈Icc 1 4, L r)<(common (next H R) x y:ℝ)) :
      ∃ r∈Icc 1 4, L r≤(selectedCost H x y r R:ℝ) := by
    by_contra! hh
    have hs := sum_le_sum (s := Icc 1 4) (fun r hr => (hh r hr).le)
    have hc : (common (next H R) x y:ℝ)≤(C:ℝ)+∑ r∈Icc 1 4, (selectedCost H x y r R:ℝ) := by
      have hb := (GreedyBatchCommonStep.common_step H R (fun e he => (hH e he).2) x y hxy).trans
        (Nat.add_le_add_right hC _)
      exact_mod_cast hb
    linarith only [hs,hc,hbad]
  apply (cover_bound p hp hp1 (Icc 1 4) (fun r R => L r≤(selectedCost H x y r R:ℝ)) _ hcover).trans
  apply sum_le_sum
  intro r hr
  exact GreedyBatchCommonBudgets.layer_tail H x y r (masses D2 D3 D4 P B r) P q
    (fun e he => (hH e he).2) (support_mass H x y D2 D3 D4 P B hH hI hP h2 h3 h4 hB r)
    hP p (L r) hp hp1 (hL r hr)

#print axioms common_tail
end
end Erdos773.GreedyBatchCommonTail
