import Submission.FiniteKernelCrossing

/-!
Configuration and witness bounds for finite first-hitting probabilities.
Only specified-target hitting bounds are assumed, so these lemmas apply to
guarded survival kernels without claiming an unrestricted inclusion law.
-/
namespace Erdos773.FiniteWitnessCrossing
open Finset FiniteKernelCrossing
set_option maxHeartbeats 2500000
noncomputable section
variable {σ α β : Type*} [Fintype σ] [DecidableEq α]

/-- Monotonicity for time-dependent events, through a finite horizon. -/
theorem hit_mono (K : ℕ → Kernel σ) (P Q : ℕ → σ → Prop) (T : ℕ)
    (hPQ : ∀ n ≤ T, ∀ x, P n x → Q n x)
    (n h : ℕ) (hnh : n+h ≤ T) (x : σ) : hit K P n h x ≤ hit K Q n h x := by
  classical
  induction h generalizing n x with
  | zero =>
    by_cases hp : P n x
    · simp only [hit, if_pos hp, if_pos (hPQ n (by omega) x hp), le_refl]
    · simpa only [hit, if_neg hp] using (hit_bounds K Q n 0 x).1
  | succ h ih =>
    by_cases hq : Q n x
    · simpa only [hit_eq_one_of_now K Q n (h+1) x hq] using (hit_bounds K P n (h+1) x).2
    · have hp : ¬P n x := fun hp => hq (hPQ n (by omega) x hp)
      simp only [hit, if_neg hp, if_neg hq]
      exact (K n).avg_mono (fun y => ih (n+1) (by omega) y) x

/-- A finite witness union bounds a first crossing, not merely a terminal
indicator. Repeated indexed witnesses need not be distinct. -/
theorem witness_bound (K : ℕ → Kernel σ) (S : Finset β)
    (P : ℕ → σ → Prop) (W : β → ℕ → σ → Prop) (T : ℕ)
    (hcover : ∀ n ≤ T, ∀ x, P n x → ∃ i ∈ S, W i n x)
    (n h : ℕ) (hnh : n+h ≤ T) (x : σ) (b : β → ℝ)
    (hb : ∀ i ∈ S, hit K (W i) n h x ≤ b i) :
    hit K P n h x ≤ ∑ i ∈ S, b i := by
  calc
    _ ≤ hit K (fun n x => ∃ i ∈ S, W i n x) n h x := hit_mono K P _ T hcover n h hnh x
    _ ≤ ∑ i ∈ S, hit K (W i) n h x := hit_union_bound K S W n h x
    _ ≤ _ := sum_le_sum hb

/-- At least k selected configurations have a selected k-subfamily. Its union
is a single target. Every required union-size hypothesis remains explicit. -/
theorem configuration_tail [DecidableEq β]
    (K : ℕ → Kernel σ) (selected : Finset α → ℕ → σ → Prop)
    (carrier : σ → Finset α) (eligible : σ → Prop) (S : Finset β) (C : β → Finset α) (k m T : ℕ)
    (hselected : ∀ U n x, eligible x → U ⊆ carrier x → selected U n x)
    (hunion : ∀ A ∈ S.powersetCard k, m ≤ (A.biUnion C).card)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (n h : ℕ) (hnh : n+h ≤ T) (x : σ)
    (htarget : ∀ A ∈ S.powersetCard k,
      hit K (selected (A.biUnion C)) n h x ≤ p^(A.biUnion C).card) :
    hit K (fun _ x => eligible x ∧ k ≤ (S.filter (fun i => C i ⊆ carrier x)).card) n h x ≤
      (S.card.choose k : ℝ)*p^m := by
  have hcover (n : ℕ) (_hn : n ≤ T) (x : σ)
      (hx : eligible x ∧ k ≤ (S.filter (fun i => C i ⊆ carrier x)).card) :
      ∃ A ∈ S.powersetCard k, selected (A.biUnion C) n x := by
    obtain ⟨A, hA, hcard⟩ := exists_subset_card_eq hx.2
    refine ⟨A, mem_powersetCard.mpr ⟨hA.trans (filter_subset _ _), hcard⟩, ?_⟩
    apply hselected _ _ _ hx.1
    exact biUnion_subset.mpr (fun i hi => (mem_filter.mp (hA hi)).2)
  have hh := witness_bound K (S.powersetCard k) _ (fun A => selected (A.biUnion C))
    T hcover n h hnh x (fun A => p^(A.biUnion C).card) htarget
  calc
    _ ≤ ∑ A ∈ S.powersetCard k, p^(A.biUnion C).card := hh
    _ ≤ ∑ _A ∈ S.powersetCard k, p^m :=
      sum_le_sum (fun A hA => pow_le_pow_of_le_one hp hp1 (hunion A hA))
    _ = _ := by simp [card_powersetCard]

#print axioms hit_mono
#print axioms witness_bound
#print axioms configuration_tail
end
end Erdos773.FiniteWitnessCrossing
