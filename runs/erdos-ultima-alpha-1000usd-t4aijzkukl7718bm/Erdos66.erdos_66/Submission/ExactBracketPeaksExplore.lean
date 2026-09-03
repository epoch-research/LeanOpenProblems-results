import Submission.ChordPeakExtensionExplore

/-! One actual Boolean set lies in every exact harmonic prefix bracket and
still has unbounded normalized representation peaks. This does not negate
the original existential conjecture. -/
namespace Erdos66ExactBracketPeaks
open Filter AdditiveCombinatorics Erdos66Fractional Erdos66Generating
  Erdos66Rounding Erdos66ClampedPrefixContinuation
  Erdos66CenteredCumulativeRounding Erdos66ChordPeakExtension
open scoped Topology Classical
set_option maxHeartbeats 2000000

noncomputable def states : ℕ → State
  | 0 => initial
  | k+1 => (step (states k) k).1

noncomputable def target (k : ℕ) : ℕ := (step (states k) k).2

lemma states_step (k : ℕ) : Extension (states k) k (states (k+1),target k) :=
  step_spec (states k) k

lemma states_cutoff_mono : Monotone (fun k ↦ (states k).T) := by
  apply monotone_nat_of_le_succ
  intro k
  exact (states_step k).1.le

lemma states_cutoff (k : ℕ) : k≤ (states k).T := by
  induction k with
  | zero => omega
  | succ k ih =>
    have hh := (states_step k).1
    dsimp only at hh
    omega

lemma states_stable (j k : ℕ) (hjk : j≤ k) (n : ℕ) (hn : n≤ (states j).T) :
    (states k).F n=(states j).F n := by
  induction k, hjk using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
    have hh := (states_step k).2.2.2.1 n (hn.trans (states_cutoff_mono hk))
    exact hh.trans ih

noncomputable def limitCumulative (n : ℕ) : ℝ := (states (n+1)).F n

lemma limit_eq_state (j n : ℕ) (hn : n≤ (states j).T) :
    limitCumulative n=(states j).F n := by
  rcases le_total j (n+1) with hj | hj
  · exact states_stable j (n+1) hj n hn
  · exact (states_stable (n+1) j hj n (by have := states_cutoff (n+1); omega)).symm

lemma limit_zero : limitCumulative 0=1/2 := (states 1).zero

lemma limit_steps : UnitSteps limitCumulative := by
  intro n
  have hT := states_cutoff (n+2)
  rw [limit_eq_state (n+2) (n+1) (by omega),limit_eq_state (n+2) n (by omega)]
  exact (states (n+2)).steps n

lemma limit_close (n : ℕ) : |limitCumulative n-(mass profile n+1/2)|≤ 1/4 :=
  (states (n+1)).close n

noncomputable def badSet : Set ℕ := rounded limitCumulative

/-- The exact integer floor/ceiling constraints hold at every prefix. -/
theorem badSet_brackets (N : ℕ) : PrefixBrackets profile badSet N :=
  rounded_original_brackets profile limitCumulative limit_steps limit_zero
    (1/4) (by norm_num) limit_close N

/-- In fact the absolute counting discrepancy is at most three quarters,
strictly less than the old allowance of eleven. -/
theorem badSet_mass_discrepancy (N : ℕ) :
    |mass (indicator badSet) N-mass profile N|≤ 3/4 := by
  rw [show badSet=rounded limitCumulative from rfl,rounded_mass _ limit_steps limit_zero]
  simpa only [show (1/2:ℝ)+1/4=3/4 by norm_num] using
    centered_floor_error (mass profile N) (limitCumulative N) (1/4) (limit_close N)

lemma badSet_rep (k : ℕ) :
    sumRep badSet (target k)=sumRep (rounded (states (k+1)).F) (target k) := by
  have hT := (states_step k).2.2.1
  dsimp only at hT
  apply Erdos66Compactness.sumRep_congr_below
  intro i hi
  change (⌊limitCumulative (i+1)⌋-⌊limitCumulative i⌋=1) ↔
    (⌊(states (k+1)).F (i+1)⌋-⌊(states (k+1)).F i⌋=1)
  rw [limit_eq_state (k+1) (i+1) (by omega),limit_eq_state (k+1) i (by omega)]

lemma target_ge (k : ℕ) : k≤ target k :=
  (states_cutoff k).trans (states_step k).2.1

/-- Every normalized height is reached arbitrarily late by this SAME set. -/
theorem badSet_peaks (M N : ℕ) :
    ∃ n : ℕ, N≤ n ∧ (M:ℝ)≤ (sumRep badSet n:ℝ)/Real.log n := by
  let k := max M N
  refine ⟨target k,(le_max_right M N).trans (target_ge k),?_⟩
  rw [badSet_rep]
  exact (by exact_mod_cast (le_max_left M N) : (M:ℝ)≤ k).trans (states_step k).2.2.2.2

 theorem badSet_no_limit (c : ℝ) :
    ¬ Tendsto (fun n ↦ (sumRep badSet n:ℝ)/Real.log n) atTop (𝓝 c) := by
  intro hc
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hc.eventually_lt_const (show c<c+1 by linarith))
  obtain ⟨M,hM⟩ := exists_nat_gt (c+1)
  obtain ⟨n,hn,hpeak⟩ := badSet_peaks M N
  have hh := hN n hn
  linarith

 theorem exists_exact_bracket_unbounded_peaks :
    ∃ A : Set ℕ, (∀ N, PrefixBrackets profile A N) ∧
      (∀ N, |mass (indicator A) N-mass profile N|≤ 3/4) ∧
      (∀ M N : ℕ, ∃ n : ℕ, N≤ n ∧ (M:ℝ)≤ (sumRep A n:ℝ)/Real.log n) ∧
      ∀ c : ℝ, ¬ Tendsto (fun n ↦ (sumRep A n:ℝ)/Real.log n) atTop (𝓝 c) :=
  ⟨badSet,badSet_brackets,badSet_mass_discrepancy,badSet_peaks,badSet_no_limit⟩

lemma badSet_error_prefix (n : ℕ) :
    |prefixSum (roundingError badSet) n|≤ 3/4 := by
  simpa only [prefixSum,roundingError,Finset.sum_sub_distrib,mass] using
    badSet_mass_discrepancy (n+1)

/-- The missing quadratic limit fails for an actual exact-bracket rounding,
not merely for an arbitrary signed error sequence. -/
theorem badSet_quadratic_error_not_zero :
    ¬ Tendsto (fun n ↦ sumConv (roundingError badSet) (roundingError badSet) n/Real.log n)
      atTop (𝓝 0) := by
  intro h
  exact badSet_no_limit 1 ((logarithmic_limit_iff_quadratic_error badSet (3/4)
    (by norm_num) badSet_error_prefix).mpr h)

end Erdos66ExactBracketPeaks
