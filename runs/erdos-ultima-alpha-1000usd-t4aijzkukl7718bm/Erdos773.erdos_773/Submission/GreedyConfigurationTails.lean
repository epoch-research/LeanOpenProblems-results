import Submission.StoppedGreedyMoments

/-!
Witness and disjoint-configuration tail bounds for the stopped greedy process.
No assertion that the process reaches the proposed stopping time is made.
-/
namespace Erdos773.GreedyConfigurationTails
open Finset GreedyHypergraphState StoppedGreedyMoments
set_option maxHeartbeats 1500000
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

def event (P : Finset α → Prop) (I : Finset α) : ℝ := by
  classical
  exact if P I then 1 else 0

omit [Fintype α] [DecidableEq α] in
lemma event_nonneg (P : Finset α → Prop) (I : Finset α) : 0 ≤ event P I := by
  classical
  unfold event
  split_ifs <;> norm_num

omit [Fintype α] [DecidableEq α] in
lemma event_le_one (P : Finset α → Prop) (I : Finset α) : event P I ≤ 1 := by
  classical
  unfold event
  split_ifs <;> norm_num

lemma event_expectation_bounds (H : Finset (Finset α)) (L n : ℕ) (P : Finset α → Prop) :
    0 ≤ expectation H L n (event P) ∧ expectation H L n (event P) ≤ 1 := by
  refine ⟨expectation_nonneg H L n (event_nonneg P),?_⟩
  have hh := expectation_mono H L n (event_le_one P)
  simpa only [expectation_const] using hh

/-- Markov's inequality for the finite expectation functional, in a form
    that permits a pointwise domination certificate for the bad event. -/
theorem markov_bound (H : Finset (Finset α)) (L n : ℕ) (f : Finset α → ℝ)
    (P : Finset α → Prop) (B : ℝ) (hB : 0 < B)
    (hdom : ∀ I, B*event P I ≤ f I) :
    expectation H L n (event P) ≤ expectation H L n f/B := by
  have hh := expectation_mono H L n hdom
  rw [expectation_mul] at hh
  apply (le_div_iff₀ hB).mpr
  simpa only [mul_comm] using hh

/-- A union bound for arbitrary indexed witnesses, with repetitions permitted. -/
theorem witness_bound {β : Type*} (H : Finset (Finset α)) (L : ℕ) (hL : 0 < L)
    (n : ℕ) (T : Finset β) (C : β → Finset α) (P : Finset α → Prop)
    (hwitness : ∀ I, P I → ∃ i ∈ T, C i ⊆ I) :
    expectation H L n (event P) ≤ ∑ i ∈ T, ((n:ℝ)/L)^(C i).card := by
  classical
  have hpoint (I : Finset α) : event P I ≤ ∑ i ∈ T, included (C i) I := by
    by_cases hp : P I
    · obtain ⟨i,hi,hsub⟩ := hwitness I hp
      have hh := single_le_sum (fun j _ => included_nonneg (C j) I) hi
      simpa only [included,if_pos hsub,event,if_pos hp] using hh
    · simp only [event,if_neg hp]
      exact sum_nonneg (fun _ _ => included_nonneg _ _)
  calc
    _ ≤ expectation H L n (fun I => ∑ i ∈ T, included (C i) I) :=
      expectation_mono H L n hpoint
    _ = ∑ i ∈ T, expectation H L n (included (C i)) := expectation_sum H L n T _
    _ ≤ _ := sum_le_sum (fun i _ => inclusion_bound H L hL n (C i))

/-- At least k selected configurations contain a k-subfamily whose entire
    union has been selected. A lower bound for each such union yields a tail. -/
theorem configuration_tail {β : Type*} [DecidableEq β]
    (H : Finset (Finset α)) (L : ℕ) (hL : 0 < L) (n : ℕ) (hn : n ≤ L)
    (T : Finset β) (C : β → Finset α) (k m : ℕ)
    (hunion : ∀ U ∈ T.powersetCard k, m ≤ (U.biUnion C).card) :
    expectation H L n (event (fun I => k ≤ (T.filter (fun i => C i ⊆ I)).card)) ≤
      (T.card.choose k:ℝ)*((n:ℝ)/L)^m := by
  classical
  have hw (I : Finset α) (hI : k ≤ (T.filter (fun i => C i ⊆ I)).card) :
      ∃ U ∈ T.powersetCard k, U.biUnion C ⊆ I := by
    obtain ⟨U,hU,hcard⟩ := exists_subset_card_eq hI
    refine ⟨U,mem_powersetCard.mpr ⟨hU.trans (filter_subset _ _),hcard⟩,?_⟩
    exact biUnion_subset.mpr (fun i hi => (mem_filter.mp (hU hi)).2)
  have hp0 : (0:ℝ) ≤ (n:ℝ)/L := by positivity
  have hp1 : (n:ℝ)/L ≤ 1 := by
    apply (div_le_one (by exact_mod_cast hL : (0:ℝ)<L)).mpr
    exact_mod_cast hn
  calc
    _ ≤ ∑ U ∈ T.powersetCard k, ((n:ℝ)/L)^(U.biUnion C).card :=
      witness_bound H L hL n (T.powersetCard k) (fun U => U.biUnion C) _ hw
    _ ≤ ∑ _U ∈ T.powersetCard k, ((n:ℝ)/L)^m :=
      sum_le_sum (fun U hU => pow_le_pow_of_le_one hp0 hp1 (hunion U hU))
    _ = _ := by simp [card_powersetCard]

/-- Binomial-type tails for pairwise disjoint configurations of size at least r.
    Independence of their inclusion events is NOT assumed. -/
theorem disjoint_configuration_tail {β : Type*} [DecidableEq β]
    (H : Finset (Finset α)) (L : ℕ) (hL : 0 < L) (n : ℕ) (hn : n ≤ L)
    (T : Finset β) (C : β → Finset α) (r k : ℕ)
    (hdis : (T:Set β).PairwiseDisjoint C) (hsize : ∀ i ∈ T, r ≤ (C i).card) :
    expectation H L n (event (fun I => k ≤ (T.filter (fun i => C i ⊆ I)).card)) ≤
      (T.card.choose k:ℝ)*((n:ℝ)/L)^(r*k) := by
  apply configuration_tail H L hL n hn T C k (r*k)
  intro U hU
  obtain ⟨hUT,hUk⟩ := mem_powersetCard.mp hU
  have hd : (U:Set β).PairwiseDisjoint C := fun i hi j hj hij => hdis (hUT hi) (hUT hj) hij
  rw [card_biUnion hd]
  calc
    r*k = ∑ _i ∈ U, r := by simp [hUk,mul_comm]
    _ ≤ _ := sum_le_sum (fun i hi => hsize i (hUT hi))

/-- Summing a finite collection of witness bounds can rule out all the bad
    events along at least one actual stopped trajectory. -/
theorem simultaneous_good_run {β : Type*}
    (H : Finset (Finset α)) (hH : ∀ e ∈ H, e.Nonempty)
    (L : ℕ) (hL : 0 < L) (n : ℕ) (T : Finset β)
    (P : β → Finset α → Prop) (b : β → ℝ)
    (hb : ∀ i ∈ T, expectation H L n (event (P i)) ≤ b i)
    (hsum : (∑ i ∈ T, b i) < 1) :
    ∃ I : Finset α, Reach H L n I ∧ Independent H I ∧
      (I.card = n ∨ (available H I).card < L) ∧ ∀ i ∈ T, ¬P i I := by
  classical
  obtain ⟨I,hI,hi⟩ := expectation_attained_below H L n (fun I => ∑ i ∈ T, event (P i) I)
  rw [expectation_sum] at hi
  have hsmall : (∑ i ∈ T, event (P i) I) < 1 :=
    hi.trans_lt ((sum_le_sum hb).trans_lt hsum)
  refine ⟨I,hI,hI.independent hH,hI.card_or_stopped hL,?_⟩
  intro i hi hp
  have hh := single_le_sum (fun j _ => event_nonneg (P j) I) hi
  have he : event (P i) I = 1 := by simp [event,hp]
  rw [he] at hh
  linarith

#print axioms markov_bound
#print axioms event_expectation_bounds
#print axioms witness_bound
#print axioms configuration_tail
#print axioms disjoint_configuration_tail
#print axioms simultaneous_good_run
end
end Erdos773.GreedyConfigurationTails
