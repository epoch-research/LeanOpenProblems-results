import Submission.GreedyTargetHazard
import Submission.FiniteKilledKernel
import Submission.GreedyFiniteKernel

/-!
First-hitting bounds for specified selected targets, up to the first failed
guard and including the failure state itself. The finite-memory kernel may
be arbitrary provided its guarded carrier projection is the actual uniform
greedy step. Numerical hazard and availability profiles remain hypotheses.
-/
namespace Erdos773.GreedySurvivalTargets
open Finset GreedyHypergraphState GreedyTargetHazard
open FiniteKernelCrossing FiniteKilledKernel
set_option maxHeartbeats 2500000
noncomputable section
variable {α σ : Type*} [Fintype α] [DecidableEq α] [Fintype σ]

/-- A ready carrier projection certificate for an arbitrary finite memory. -/
def UniformOnGuard (H : Finset (Finset α)) (K : ℕ → Kernel σ)
    (G : ℕ → σ → Prop) (carrier : σ → Finset α) (T : ℕ) : Prop :=
  ∀ n < T, ∀ x, G n x →
    (available H (carrier x)).Nonempty ∧
    ∀ f : Finset α → ℝ, (K n).avg (fun y => f (carrier y)) x =
      (∑ v ∈ available H (carrier x), f (insert v (carrier x))) /
        (available H (carrier x)).card

/-- All needed local numerical hypotheses. The overlap correction is paid
for the maximum target size k, not just for individual vertex targets. -/
def HazardProfile (H : Finset (Finset α)) (G : ℕ → σ → Prop)
    (carrier : σ → Finset α) (T k : ℕ) (r : ℕ → ℝ)
    (l : ℕ → σ → ℝ) (C : ℕ → σ → ℕ) : Prop :=
  (∀ n ≤ T, 0 ≤ r n) ∧
  ∀ n < T, ∀ x, G n x →
    (∀ u ∈ available H (carrier x), l n x ≤ (closes H (carrier x) u).card) ∧
    (∀ u ∈ available H (carrier x), ∀ v ∈ available H (carrier x), u ≠ v →
      (closes H (carrier x) u ∩ closes H (carrier x) v).card ≤ C n x) ∧
    1 ≤ (available H (carrier x)).card * (r n-r (n+1)) +
      (l n x-((k:ℝ)-1)/2*C n x)*r (n+1)

/-- Exact finite first-hit estimate. It neither freezes a positive potential
at a dead target nor assumes independence of selections. -/
theorem hit_target (H : Finset (Finset α)) (K : ℕ → Kernel σ)
    (G : ℕ → σ → Prop) (carrier : σ → Finset α) (T k : ℕ)
    (hK : UniformOnGuard H K G carrier T) (r : ℕ → ℝ)
    (l : ℕ → σ → ℝ) (C : ℕ → σ → ℕ)
    (hprofile : HazardProfile H G carrier T k r l C)
    (U : Finset α) (hU : U.card ≤ k)
    (n h : ℕ) (hnh : n+h ≤ T) (x : σ) :
    hit (fun n => kill (K n) (G n))
      (fun _ => liftEvent (fun x => U ⊆ carrier x)) n h (some x) ≤
      value H U (carrier x) (r n) := by
  have hh := hit_le_guarded_potential K G (fun _ x => U ⊆ carrier x)
    (fun n x => value H U (carrier x) (r n)) T 1 (by norm_num)
    (fun n hn x => value_nonneg H U (carrier x) (hprofile.1 n hn))
    (by
      intro n hn x hx
      obtain ⟨hne, havg⟩ := hK n hn x hx
      dsimp only
      rw [havg (fun I => value H U I (r (n+1)))]
      by_cases hB : U \ carrier x ⊆ available H (carrier x)
      · obtain ⟨hl, hC, hsc⟩ := hprofile.2 n hn x hx
        exact average_le_value H U (carrier x) (r n) (r (n+1)) (l n x) (C n x) k
          (hprofile.1 n (by omega)) (hprofile.1 (n+1) (by omega)) hne
          ((card_le_card sdiff_subset).trans hU)
          (fun u hu => hl u (hB hu)) (fun u hu v hv huv => hC u (hB hu) v (hB hv) huv) hsc
      · have hz : (∑ v ∈ available H (carrier x), value H U (insert v (carrier x)) (r (n+1))) = 0 :=
          sum_eq_zero (fun v hv => value_eq_zero_of_dead hv hB (r (n+1)))
        rw [hz, zero_div, value, if_neg hB])
    (fun _ _ _ hsub => (value_eq_one hsub _).ge) n h hnh x
  simpa only [div_one] using hh

/-- From the empty selected carrier, the cost is r(0)^|U|. A target which is
initially unavailable only improves this inequality. -/
theorem hit_target_from_empty (H : Finset (Finset α)) (K : ℕ → Kernel σ)
    (G : ℕ → σ → Prop) (carrier : σ → Finset α) (T k : ℕ)
    (hK : UniformOnGuard H K G carrier T) (r : ℕ → ℝ)
    (l : ℕ → σ → ℝ) (C : ℕ → σ → ℕ)
    (hprofile : HazardProfile H G carrier T k r l C)
    (U : Finset α) (hU : U.card ≤ k) (x : σ) (hx : carrier x = ∅) :
    hit (fun n => kill (K n) (G n))
      (fun _ => liftEvent (fun x => U ⊆ carrier x)) 0 T (some x) ≤ (r 0)^U.card := by
  apply (hit_target H K G carrier T k hK r l C hprofile U hU 0 T (by omega) x).trans
  rw [hx, value, sdiff_empty]
  split_ifs
  · exact le_rfl
  · exact pow_nonneg (hprofile.1 0 (Nat.zero_le _)) _

/-- The existing lifted greedy kernel supplies the carrier interface, whenever
the new killing guard implies readiness. The memory update may be correlated
with every choice. -/
theorem uniform_lifted [DecidableEq σ] (H : Finset (Finset α)) (L T : ℕ)
    (carrier : σ → Finset α) (next : ℕ → σ → Option α → σ)
    (hnext : ∀ n x a, a ∈ GreedyFiniteKernel.actions H L (carrier x) →
      carrier (next n x a) = GreedyFiniteKernel.move (carrier x) a)
    (G : ℕ → σ → Prop)
    (hready : ∀ n < T, ∀ x, G n x → StoppedGreedyMoments.Ready H L (carrier x)) :
    UniformOnGuard H (fun n => GreedyFiniteKernel.liftedKernel H L carrier (next n)) G carrier T := by
  classical
  intro n hn x hx
  have hr := hready n hn x hx
  refine ⟨hr.2, ?_⟩
  intro f
  rw [GreedyFiniteKernel.lifted_avg H L carrier (next n) (hnext n),
    StoppedGreedyMoments.step, if_pos hr]

#print axioms hit_target
#print axioms hit_target_from_empty
#print axioms uniform_lifted
end
end Erdos773.GreedySurvivalTargets
