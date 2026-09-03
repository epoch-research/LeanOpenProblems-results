import Submission.GreedySurvivalTargets
import Submission.FiniteWitnessCrossing
import Submission.GreedyWitnessPacking

/-!
Witness packing with a capped survival-aware target law. All events are
first crossings in the lifted state space. The target-size cap is explicit,
so the common-neighbor correction in the hazard profile is not forgotten
when many individual witnesses are packed together.
-/
namespace Erdos773.GreedySurvivalWitnesses
open Finset FiniteKernelCrossing FiniteKilledKernel GreedySurvivalTargets
set_option maxHeartbeats 2500000
noncomputable section
variable {α σ β : Type*} [DecidableEq α] [Fintype σ]

/-- A specified-target law, only up to a stated maximum target cardinality. -/
def TargetLaw (K : ℕ → Kernel (Option σ)) (carrier : σ → Finset α)
    (n h : ℕ) (x : σ) (p : ℝ) (cap : ℕ) : Prop :=
  ∀ U : Finset α, U.card ≤ cap →
    hit K (fun _ => liftEvent (fun x => U ⊆ carrier x)) n h (some x) ≤ p^U.card

/-- The completed hazard theorem supplies exactly this capped target law. -/
theorem law_of_hazard [Fintype α] (H : Finset (Finset α)) (K : ℕ → Kernel σ)
    (G : ℕ → σ → Prop) (carrier : σ → Finset α) (T cap : ℕ)
    (hK : UniformOnGuard H K G carrier T) (r : ℕ → ℝ)
    (l : ℕ → σ → ℝ) (C : ℕ → σ → ℕ)
    (hprofile : HazardProfile H G carrier T cap r l C)
    (x : σ) (hx : carrier x = ∅) :
    TargetLaw (fun n => kill (K n) (G n)) carrier 0 T x (r 0) cap :=
  fun U hU => hit_target_from_empty H K G carrier T cap hK r l C hprofile U hU x hx

omit [DecidableEq α] in
/-- Indexed finite witness union for arbitrary time-dependent recorded events. -/
theorem witness_bound (K : ℕ → Kernel (Option σ)) (carrier : σ → Finset α)
    (n h : ℕ) (x : σ) (p : ℝ) (cap : ℕ) (hlaw : TargetLaw K carrier n h x p cap)
    (S : Finset β) (C : β → Finset α) (hsize : ∀ i ∈ S, (C i).card ≤ cap)
    (P : ℕ → σ → Prop)
    (hcover : ∀ m ≤ n+h, ∀ y, P m y → ∃ i ∈ S, C i ⊆ carrier y) :
    hit K (fun m => liftEvent (P m)) n h (some x) ≤ ∑ i ∈ S, p^(C i).card := by
  apply FiniteWitnessCrossing.witness_bound K S _
    (fun i _ => liftEvent (fun y => C i ⊆ carrier y)) (n+h) _ n h le_rfl (some x)
    (fun i => p^(C i).card) (fun i hi => hlaw (C i) (hsize i hi))
  intro m hm y hy
  cases y with
  | none => exact hy.elim
  | some y => exact hcover m hm y hy

/-- Packing at first crossing, with all target unions bounded by the cap. -/
theorem packing_tail [DecidableEq β]
    (K : ℕ → Kernel (Option σ)) (carrier : σ → Finset α)
    (n h : ℕ) (x : σ) (p : ℝ) (cap : ℕ) (hlaw : TargetLaw K carrier n h x p cap)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (S : Finset β) (C : β → Finset α) (r M s k : ℕ)
    (hne : ∀ i ∈ S, (C i).Nonempty)
    (hsize : ∀ i ∈ S, (C i).card ≤ r)
    (hlower : ∀ i ∈ S, s ≤ (C i).card)
    (hinc : ∀ a, (S.filter (fun i => a ∈ C i)).card ≤ M)
    (hcap : r*(k+1) ≤ cap) :
    hit K (fun _ => liftEvent (fun y => r*M*k < (S.filter (fun i => C i ⊆ carrier y)).card))
      n h (some x) ≤ (S.card.choose (k+1) : ℝ)*p^(s*(k+1)) := by
  classical
  let F := (S.powersetCard (k+1)).filter (fun U : Finset β => (U : Set β).PairwiseDisjoint C)
  have hw (m : ℕ) (_hm : m ≤ n+h) (y : σ)
      (hy : r*M*k < (S.filter (fun i => C i ⊆ carrier y)).card) :
      ∃ U ∈ F, U.biUnion C ⊆ carrier y := by
    obtain ⟨U, hU, hd, hUI⟩ := GreedyWitnessPacking.selected_packing_witness
      S C r M k hne hsize hinc (carrier y) hy
    exact ⟨U, mem_filter.mpr ⟨hU, hd⟩, hUI⟩
  have hc (U : Finset β) (hU : U ∈ F) : (U.biUnion C).card ≤ cap := by
    obtain ⟨hUT, hUk⟩ := mem_powersetCard.mp (mem_filter.mp hU).1
    calc
      _ ≤ ∑ i ∈ U, (C i).card := card_biUnion_le
      _ ≤ ∑ _i ∈ U, r := sum_le_sum (fun i hi => hsize i (hUT hi))
      _ = r*(k+1) := by simp [hUk, mul_comm]
      _ ≤ _ := hcap
  have hlo (U : Finset β) (hU : U ∈ F) : s*(k+1) ≤ (U.biUnion C).card := by
    obtain ⟨hU, hd⟩ := mem_filter.mp hU
    obtain ⟨hUT, hUk⟩ := mem_powersetCard.mp hU
    rw [card_biUnion hd]
    calc
      s*(k+1) = ∑ _i ∈ U, s := by simp [hUk, mul_comm]
      _ ≤ _ := sum_le_sum (fun i hi => hlower i (hUT hi))
  calc
    _ ≤ ∑ U ∈ F, p^(U.biUnion C).card := witness_bound K carrier n h x p cap hlaw F _ hc _ hw
    _ ≤ ∑ _U ∈ F, p^(s*(k+1)) :=
      sum_le_sum (fun U hU => pow_le_pow_of_le_one hp hp1 (hlo U hU))
    _ = (F.card : ℝ)*p^(s*(k+1)) := by simp
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hp _)
      have hh := card_filter_le (s := S.powersetCard (k+1))
        (p := fun U : Finset β => (U : Set β).PairwiseDisjoint C)
      rw [card_powersetCard] at hh
      exact_mod_cast hh

/-- Exponential form of the same first-crossing packing bound. -/
theorem packing_exponential_tail [DecidableEq β]
    (K : ℕ → Kernel (Option σ)) (carrier : σ → Finset α)
    (n h : ℕ) (x : σ) (p : ℝ) (cap : ℕ) (hlaw : TargetLaw K carrier n h x p cap)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (S : Finset β) (C : β → Finset α) (r M s k : ℕ)
    (hne : ∀ i ∈ S, (C i).Nonempty)
    (hsize : ∀ i ∈ S, (C i).card ≤ r)
    (hlower : ∀ i ∈ S, s ≤ (C i).card)
    (hinc : ∀ a, (S.filter (fun i => a ∈ C i)).card ≤ M)
    (hcap : r*(k+1) ≤ cap) :
    hit K (fun _ => liftEvent (fun y => r*M*k < (S.filter (fun i => C i ⊆ carrier y)).card))
      n h (some x) ≤ (3*S.card*p^s/(k+1))^(k+1) := by
  have hh := (packing_tail K carrier n h x p cap hlaw hp hp1 S C r M s k hne hsize hlower hinc hcap).trans
    (GreedyWitnessPacking.choose_mul_pow_le S.card (k+1) s (by omega) p hp)
  simpa only [Nat.cast_add, Nat.cast_one] using hh

#print axioms law_of_hazard
#print axioms witness_bound
#print axioms packing_tail
#print axioms packing_exponential_tail
end
end Erdos773.GreedySurvivalWitnesses
