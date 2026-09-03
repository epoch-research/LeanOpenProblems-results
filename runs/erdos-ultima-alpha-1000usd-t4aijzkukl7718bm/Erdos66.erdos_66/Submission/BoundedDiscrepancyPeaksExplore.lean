import Submission.ReflectionStateExplore

/-! A genuine 0/1 rounding of the harmonic fractional profile with uniformly
bounded prefix discrepancy and unbounded normalized representation peaks.
This refutes an unconditional implication from bounded rounding discrepancy;
it neither disproves Erdős 66 nor decides the canonical floor rounding. -/
namespace Erdos66BoundedDiscrepancyPeaks
open Filter AdditiveCombinatorics Erdos66Fractional Erdos66Generating Erdos66Rounding
  Erdos66Counting Erdos66ReflectionRoundingPatch Erdos66SetIntervalReplacement
  Erdos66LargeReflectionPatch Erdos66Compactness Erdos66ReflectionState
open scoped Topology Classical
set_option maxHeartbeats 1000000

noncomputable def states : ℕ → State
  | 0 => initial
  | k+1 => (step (states k) k).1

noncomputable def target (k : ℕ) : ℕ := (step (states k) k).2

lemma states_step (k : ℕ) :
    (states k).T < (states (k+1)).T ∧ (states k).T ≤ target k ∧
      target k < (states (k+1)).T ∧
      (∀ i, i < (states k).T → (i ∈ (states (k+1)).A ↔ i ∈ (states k).A)) ∧
      (k : ℝ) ≤ (sumRep (states (k+1)).A (target k) : ℝ)/Real.log (target k) :=
  step_spec (states k) k

lemma states_cutoff (k : ℕ) : k ≤ (states k).T := by
  induction k with
  | zero => omega
  | succ k ih => have hh := (states_step k).1; omega

lemma states_mem_stable (j k : ℕ) (hjk : j ≤ k) (i : ℕ) (hi : i < (states j).T) :
    i ∈ (states k).A ↔ i ∈ (states j).A := by
  have hmono : Monotone (fun n ↦ (states n).T) :=
    monotone_nat_of_le_succ (fun n ↦ (states_step n).1.le)
  induction k, hjk using Nat.le_induction with
  | base => rfl
  | succ k hjk ih =>
    exact ((states_step k).2.2.2.1 i (hi.trans_le (hmono hjk))).trans ih

noncomputable def badRounding : Set ℕ := {i | i ∈ (states (i+1)).A}

lemma badRounding_mem (j i : ℕ) (hi : i < (states j).T) :
    i ∈ badRounding ↔ i ∈ (states j).A := by
  have hi' : i < (states (i+1)).T := lt_of_lt_of_le (Nat.lt_succ_self i) (states_cutoff (i+1))
  exact (states_mem_stable (i+1) (max (i+1) j) (le_max_left _ _) i hi').symm.trans
    (states_mem_stable j (max (i+1) j) (le_max_right _ _) i hi)

lemma badRounding_count (N : ℕ) : count badRounding N = count (states N).A N := by
  unfold count
  congr 1
  ext i
  simp only [mem_cutoff]
  apply and_congr_right
  intro hi
  exact badRounding_mem N i (hi.trans_le (states_cutoff N))

theorem badRounding_discrepancy (N : ℕ) :
    |(count badRounding N : ℝ)-cumulative profile N| ≤ 11 := by
  rw [badRounding_count]
  exact (states N).discrepancy N

lemma badRounding_rep (k : ℕ) :
    sumRep badRounding (target k) = sumRep (states (k+1)).A (target k) := by
  apply sumRep_congr_below
  intro i hi
  exact badRounding_mem (k+1) i (hi.trans_lt (states_step k).2.2.1)

lemma target_ge (k : ℕ) : k ≤ target k :=
  (states_cutoff k).trans (states_step k).2.1

theorem badRounding_peaks (M N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ (M : ℝ) ≤ (sumRep badRounding n : ℝ)/Real.log n := by
  let k := max M N
  refine ⟨target k,(le_max_right M N).trans (target_ge k),?_⟩
  rw [badRounding_rep]
  have hMk : (M : ℝ) ≤ k := by exact_mod_cast (le_max_left M N)
  exact hMk.trans (states_step k).2.2.2.2

theorem badRounding_no_limit (c : ℝ) :
    ¬ Tendsto (fun n ↦ (sumRep badRounding n : ℝ)/Real.log n) atTop (𝓝 c) := by
  intro h
  obtain ⟨M,hM⟩ := exists_nat_gt (c+1)
  have he := h.eventually_lt_const (show c < c+1 by linarith)
  obtain ⟨N,hN⟩ := eventually_atTop.mp he
  obtain ⟨n,hn,hpeak⟩ := badRounding_peaks M N
  have hh := hN n hn
  linarith

theorem exists_bounded_discrepancy_unbounded_peaks :
    ∃ A : Set ℕ,
      (∀ N, |(count A N : ℝ)-cumulative profile N| ≤ 11) ∧
      (∀ M N : ℕ, ∃ n : ℕ, N ≤ n ∧ (M : ℝ) ≤ (sumRep A n : ℝ)/Real.log n) ∧
      (∀ c : ℝ, ¬ Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c)) :=
  ⟨badRounding,badRounding_discrepancy,badRounding_peaks,badRounding_no_limit⟩

theorem badRounding_error_prefix (n : ℕ) :
    |prefixSum (roundingError badRounding) n| ≤ 11 := by
  have hh := badRounding_discrepancy (n+1)
  rw [count_sum] at hh
  simpa only [prefixSum,roundingError,cumulative,Finset.sum_sub_distrib] using hh

theorem badRounding_quadratic_error_not_zero :
    ¬ Tendsto (fun n ↦ sumConv (roundingError badRounding) (roundingError badRounding) n /
      Real.log n) atTop (𝓝 0) := by
  intro h
  exact badRounding_no_limit 1
    ((logarithmic_limit_iff_quadratic_error badRounding 11 (by norm_num)
      badRounding_error_prefix).mpr h)

end Erdos66BoundedDiscrepancyPeaks
