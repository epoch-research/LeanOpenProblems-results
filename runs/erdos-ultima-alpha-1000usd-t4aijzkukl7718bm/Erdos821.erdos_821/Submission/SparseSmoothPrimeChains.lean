import Submission.LargeChildPropagation
import Submission.HigherRootReduction

/-!
# A prime-chain consequence of a hypothetical counterexample to Erdos 821

If the conjecture is false, some root-smooth prime set has a convergent power
series below one. Every fixed-depth large-child ancestor set is then power
sparse. Its prime complement retains reciprocal divergence and contains paths
of the prescribed length avoiding that smooth set.

The negation of the conjecture is an explicit hypothesis throughout. These
results prove neither it nor a contradiction from it.
-/

open Nat Filter
open scoped Classical BigOperators

namespace Erdos821

set_option maxHeartbeats 2000000

def rootSmoothPrimeSet (k : ℕ) : Set ℕ :=
  {p | p.Prime ∧ p-1 ∈ smoothShiftedPredecessors k}

lemma summable_rootSmoothPrimeSet (k : ℕ) (b : ℝ) (hb : 0 ≤ b)
    (H : Summable ((smoothShiftedPredecessors k).indicator
      (fun n : ℕ => (n : ℝ)^(-b)))) :
    Summable ((rootSmoothPrimeSet k).indicator (fun p : ℕ => (p : ℝ)^(-b))) := by
  apply (summable_nat_add_iff 1).mp
  apply H.of_nonneg_of_le
    (fun n => Set.indicator_nonneg (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _) (n+1))
  intro n
  by_cases hn : n+1 ∈ rootSmoothPrimeSet k
  · have hn0 : 0 < n := by have := hn.1.two_le; omega
    have hns : n ∈ smoothShiftedPredecessors k := by
      simpa only [Nat.add_sub_cancel] using hn.2
    rw [Set.indicator_of_mem hn, Set.indicator_of_mem hns]
    exact Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hn0)
      (by exact_mod_cast (Nat.le_succ n)) (by linarith)
  · rw [Set.indicator_of_notMem hn]
    exact Set.indicator_nonneg (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _) n

lemma prime_outside_rootSmoothPrimeSet_has_large_child (k p : ℕ)
    (hp : p.Prime) (hpA : p ∉ rootSmoothPrimeSet k) :
    ∃ q : ℕ, q.Prime ∧ q ∣ p-1 ∧ p-1 < q^k := by
  have hns : ¬ (∀ q ∈ (p-1).primeFactors, q^k ≤ p-1) := by
    intro hs
    apply hpA
    refine ⟨hp, ?_, hs⟩
    simpa only [Nat.sub_add_cancel hp.pos] using hp
  push_neg at hns
  obtain ⟨q, hq, hqsize⟩ := hns
  exact ⟨q, Nat.prime_of_mem_primeFactors hq, Nat.dvd_of_mem_primeFactors hq, hqsize⟩

/-- Every prime reaches the smooth set after finitely many large-child
steps. The depth is allowed to depend on the prime. -/
lemma prime_mem_some_root_smooth_ancestor_layer (k p : ℕ) (hp : p.Prime) :
    ∃ L : ℕ, p ∈ largeChildLayer k (rootSmoothPrimeSet k) L := by
  induction p using Nat.strong_induction_on with
  | h p ih =>
    by_cases hpA : p ∈ rootSmoothPrimeSet k
    · exact ⟨0, hpA⟩
    · obtain ⟨q, hq, hqd, hqsize⟩ :=
        prime_outside_rootSmoothPrimeSet_has_large_child k p hp hpA
      have hqle : q ≤ p-1 := Nat.le_of_dvd (by have := hp.two_le; omega) hqd
      have hq_lt : q < p := by have := hp.two_le; omega
      obtain ⟨L, hqL⟩ := ih q hq_lt hq
      exact ⟨L+1, Or.inr ⟨hp, q, hqL, hq, hqd, hqsize.le⟩⟩

lemma root_smooth_ancestor_layers_cover_primes (k : ℕ) :
    (⋃ L : ℕ, largeChildLayer k (rootSmoothPrimeSet k) L) = {p : ℕ | p.Prime} := by
  ext p
  constructor
  · intro hp
    obtain ⟨L, hpL⟩ := Set.mem_iUnion.mp hp
    induction L with
    | zero => exact hpL.1
    | succ L ih =>
      rcases hpL with hprev | hparent
      · exact ih hprev
      · exact hparent.1
  · intro hp
    exact Set.mem_iUnion.mpr (prime_mem_some_root_smooth_ancestor_layer k p hp)

/-- A hypothetical failure yields one power-sparse root-smooth prime set.
The previously proved root-two divergence ensures that k can be at least three. -/
theorem exists_sparse_rootSmoothPrimeSet_of_negation
    (Hneg : ¬ (∀ ε > (0 : ℝ),
      {n : ℕ | (g n : ℝ) > (n : ℝ)^(1-ε)}.Infinite)) :
    ∃ k : ℕ, 3 ≤ k ∧ ∃ b : ℝ, 0 ≤ b ∧ b < 1 ∧
      Summable ((rootSmoothPrimeSet k).indicator (fun p : ℕ => (p : ℝ)^(-b))) := by
  have Hnot : ¬ (∀ k : ℕ, 3 ≤ k → ∀ s : ℝ, s < 1 →
      ¬Summable ((smoothShiftedPredecessors k).indicator
        (fun d : ℕ => (d : ℝ)^(-s)))) := by
    intro H
    exact Hneg (erdos_821_iff_higher_root_series.mpr H)
  push_neg at Hnot
  obtain ⟨k, hk, s, hs, Hsum⟩ := Hnot
  let b : ℝ := max 0 s
  have hb : 0 ≤ b := le_max_left _ _
  have hb1 : b < 1 := max_lt (by norm_num) hs
  refine ⟨k, hk, b, hb, hb1, summable_rootSmoothPrimeSet k b hb ?_⟩
  exact summable_set_power_mono (smoothShiftedPredecessors k) s b (le_max_right _ _) Hsum

/-- An explicit summability exponent survives at every fixed ancestor depth.
No assertion uniform in increasing L is made. -/
theorem negation_forces_sparse_large_child_layers
    (Hneg : ¬ (∀ ε > (0 : ℝ),
      {n : ℕ | (g n : ℝ) > (n : ℝ)^(1-ε)}.Infinite)) :
    ∃ k : ℕ, 3 ≤ k ∧ ∃ b : ℝ, 0 ≤ b ∧ b < 1 ∧
      (∀ L : ℕ, Summable ((largeChildLayer k (rootSmoothPrimeSet k) L).indicator
        (fun p : ℕ => (p : ℝ)^(-(1-(1-b)/(2*(k : ℝ))^L))))) ∧
      ∀ L : ℕ, ¬Summable
        (({p : ℕ | p.Prime ∧ p ∉ largeChildLayer k (rootSmoothPrimeSet k) L} : Set ℕ).indicator
          (fun p : ℕ => 1/(p : ℝ))) := by
  obtain ⟨k, hk, b, hb, hb1, Hsum⟩ := exists_sparse_rootSmoothPrimeSet_of_negation Hneg
  have hk1 : 1 ≤ k := by omega
  refine ⟨k, hk, b, hb, hb1, ?_, ?_⟩
  · intro L
    simpa only [largeChildLayerExponent_eq k hk1 b L] using
      summable_largeChildLayer k hk1 (rootSmoothPrimeSet k) b hb hb1 Hsum L
  · exact not_summable_reciprocal_outside_largeChildLayer k hk1
      (rootSmoothPrimeSet k) b hb hb1 Hsum

/-- Under the explicit hypothetical negation, every fixed path length is
realized by a reciprocal-divergent set of prime starting vertices. -/
theorem negation_forces_reciprocal_many_avoiding_paths
    (Hneg : ¬ (∀ ε > (0 : ℝ),
      {n : ℕ | (g n : ℝ) > (n : ℝ)^(1-ε)}.Infinite)) :
    ∃ k : ℕ, 3 ≤ k ∧ ∀ L : ℕ,
      ¬Summable (({p : ℕ | largeChildAvoidingPath k (rootSmoothPrimeSet k) L p} : Set ℕ).indicator
        (fun p : ℕ => 1/(p : ℝ))) := by
  obtain ⟨k, hk, b, hb, hb1, Hsum⟩ := exists_sparse_rootSmoothPrimeSet_of_negation Hneg
  refine ⟨k, hk, ?_⟩
  intro L Hpath
  apply not_summable_reciprocal_outside_largeChildLayer k (by omega)
    (rootSmoothPrimeSet k) b hb hb1 Hsum L
  apply Hpath.of_nonneg_of_le
    (fun p => Set.indicator_nonneg (fun p _ => div_nonneg (by norm_num) (Nat.cast_nonneg p)) p)
  intro p
  by_cases hp : p ∈ {p : ℕ | p.Prime ∧ p ∉ largeChildLayer k (rootSmoothPrimeSet k) L}
  · have hpath : p ∈ {p : ℕ | largeChildAvoidingPath k (rootSmoothPrimeSet k) L p} :=
      outside_largeChildLayer_has_avoiding_path k (rootSmoothPrimeSet k)
        (prime_outside_rootSmoothPrimeSet_has_large_child k) L p hp.1 hp.2
    rw [Set.indicator_of_mem hp, Set.indicator_of_mem hpath]
  · rw [Set.indicator_of_notMem hp]
    exact Set.indicator_nonneg (fun p _ => div_nonneg (by norm_num) (Nat.cast_nonneg p)) p

end Erdos821
