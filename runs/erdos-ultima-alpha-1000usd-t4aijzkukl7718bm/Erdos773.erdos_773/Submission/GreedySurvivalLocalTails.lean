import Submission.GreedySurvivalWitnesses
import Submission.GreedyLocalDuplicateTails

/-!
Local duplicate and common-neighbor first-crossing tails from the capped
survival law. These are true guard-stopped tails; they do NOT assert that the
unrestricted selected carrier satisfies the same sharper inclusion law.
-/
namespace Erdos773.GreedySurvivalLocalTails
open Finset FiniteKernelCrossing FiniteKilledKernel GreedySurvivalWitnesses
open GreedyHypergraphState HypergraphDegreeTrim FourUniformRegularization
set_option maxHeartbeats 2500000
noncomputable section
variable {α σ : Type*} [Fintype α] [DecidableEq α] [Fintype σ]

/-- Uniform-prefix duplicate witnesses, with the survival probability p. -/
theorem prefix_duplicate_tail {H : Finset (Finset α)}
    (h4 : ∀ e ∈ H, e.card = 4)
    (h2 : ∀ e ∈ H, ∀ f ∈ H, e ≠ f → (e ∩ f).card ≤ 2)
    (u : α) (D P : ℕ) (hD : degree H u ≤ D)
    (hP : ∀ a b : α, a ≠ b → pairDegree H a b ≤ P)
    (K : ℕ → Kernel (Option σ)) (carrier : σ → Finset α)
    (n h : ℕ) (x : σ) (p : ℝ) (cap k : ℕ)
    (hlaw : TargetLaw K carrier n h x p cap) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hcap : 4*(k+1) ≤ cap) :
    hit K (fun _ => liftEvent (fun y =>
      GreedyLocalDuplicateTails.prefixBad H u (16*P^2*k) (carrier y))) n h (some x) ≤
      (9*D*P*p^4/(k+1))^(k+1) := by
  let S := GreedyLocalDuplicateTails.patterns H u
  let C := GreedyLocalDuplicateTails.witness (α := α)
  have hs (i : GreedyCommonNeighbors.Pattern α) (hi : i ∈ S) : (C i).card = 4 :=
    GreedyLocalDuplicateTails.witness_card h4 h2 hi
  have hmono : hit K (fun _ => liftEvent (fun y =>
      GreedyLocalDuplicateTails.prefixBad H u (16*P^2*k) (carrier y))) n h (some x) ≤
      hit K (fun _ => liftEvent (fun y =>
        4*(4*P^2)*k < (S.filter (fun i => C i ⊆ carrier y)).card)) n h (some x) := by
    apply FiniteWitnessCrossing.hit_mono K _ _ (n+h) _ n h le_rfl (some x)
    intro m hm y hy
    cases y with
    | none => exact hy.elim
    | some y =>
      obtain ⟨I, hI, hb⟩ := hy
      have hh := hb.trans_le ((GreedyLocalDuplicateTails.excess_bound H I u).trans
        (GreedyLocalDuplicateTails.cost_mono H u hI))
      change 4*(4*P^2)*k < GreedyLocalDuplicateTails.cost H u (carrier y)
      convert hh using 1
      ring
  have ht := packing_exponential_tail K carrier n h x p cap hlaw hp hp1 S C 4 (4*P^2) 4 k
    (fun i hi => card_pos.mp (by rw [hs i hi]; decide))
    (fun i hi => (hs i hi).le) (fun i hi => (hs i hi).ge)
    (fun a => GreedyLocalDuplicateTails.witness_incidence h4 u a P hP) hcap
  apply (hmono.trans ht).trans
  have hc : (S.card : ℝ) ≤ 3*D*P := by
    exact_mod_cast GreedyLocalDuplicateTails.patterns_card_le h4 u D P hD hP
  have hbase : 3*S.card*p^4/(k+1) ≤ 9*D*P*p^4/(k+1) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hh := mul_le_mul_of_nonneg_right hc (show 0 ≤ 3*p^4 by positivity)
    nlinarith only [hh]
  exact pow_le_pow_left₀ (by positivity) hbase (k+1)

/-- Common-neighbor witnesses have support size at least three. Their upper
support size, four, is still charged against the hazard's target-size cap. -/
theorem prefix_common_tail {H : Finset (Finset α)}
    (h4 : ∀ e ∈ H, e.card = 4)
    (h2 : ∀ e ∈ H, ∀ f ∈ H, e ≠ f → (e ∩ f).card ≤ 2)
    (u v : α) (huv : u ≠ v) (D P : ℕ) (hD : degree H u ≤ D)
    (hP : ∀ a b : α, a ≠ b → pairDegree H a b ≤ P)
    (K : ℕ → Kernel (Option σ)) (carrier : σ → Finset α)
    (n h : ℕ) (x : σ) (p : ℝ) (cap k : ℕ)
    (hlaw : TargetLaw K carrier n h x p cap) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hcap : 4*(k+1) ≤ cap) :
    hit K (fun _ => liftEvent (fun y =>
      GreedyCommonNeighbors.prefixBad H u v (16*P^2*k) (carrier y))) n h (some x) ≤
      (9*D*P*p^3/(k+1))^(k+1) := by
  let S := GreedyCommonNeighbors.patterns H u v
  let C := GreedyCommonNeighbors.witness u v
  have hs (i : GreedyCommonNeighbors.Pattern α) (hi : i ∈ S) :
      3 ≤ (C i).card ∧ (C i).card ≤ 4 := GreedyCommonNeighbors.witness_card_bounds h4 h2 hi
  have hmono : hit K (fun _ => liftEvent (fun y =>
      GreedyCommonNeighbors.prefixBad H u v (16*P^2*k) (carrier y))) n h (some x) ≤
      hit K (fun _ => liftEvent (fun y =>
        4*(4*P^2)*k < (S.filter (fun i => C i ⊆ carrier y)).card)) n h (some x) := by
    apply FiniteWitnessCrossing.hit_mono K _ _ (n+h) _ n h le_rfl (some x)
    intro m hm y hy
    cases y with
    | none => exact hy.elim
    | some y =>
      obtain ⟨I, hI, hu, hv, hb⟩ := hy
      have hh := hb.trans_le ((GreedyCommonNeighbors.common_degree_bound huv hu hv).trans
        (GreedyCommonNeighbors.patternCost_mono H u v hI))
      change 4*(4*P^2)*k < GreedyCommonNeighbors.patternCost H u v (carrier y)
      convert hh using 1
      ring
  have ht := packing_exponential_tail K carrier n h x p cap hlaw hp hp1 S C 4 (4*P^2) 3 k
    (fun i hi => card_pos.mp (by have := (hs i hi).1; omega))
    (fun i hi => (hs i hi).2) (fun i hi => (hs i hi).1)
    (fun a => GreedyCommonNeighbors.witness_incidence h4 u v a P hP) hcap
  apply (hmono.trans ht).trans
  have hc : (S.card : ℝ) ≤ 3*D*P := by
    exact_mod_cast GreedyCommonNeighbors.patterns_card_le h4 u v D P hD hP
  have hbase : 3*S.card*p^3/(k+1) ≤ 9*D*P*p^3/(k+1) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hh := mul_le_mul_of_nonneg_right hc (show 0 ≤ 3*p^3 by positivity)
    nlinarith only [hh]
  exact pow_le_pow_left₀ (by positivity) hbase (k+1)

#print axioms prefix_duplicate_tail
#print axioms prefix_common_tail
end
end Erdos773.GreedySurvivalLocalTails
