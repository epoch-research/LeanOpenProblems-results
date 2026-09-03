import Submission.RefinedPartitionObstruction

/-! A finite stationary transition model whose low-mass inclusion moments
factor at every positive gap, but whose largest-label transition is biased.
This is NOT an arithmetic counterexample to Erdős 371. In particular the
finite model has positive diagonal mass and does not model near-tie rarity.
It rules out extending low-observable gap invariance to arbitrary nonlinear
observables without a further argument. -/

namespace Erdos371.StationaryMomentObstruction
open Finset
open RefinedPartitionObstruction (largeParts tailType observations mem_observations_iff)

def mergeDirection : Fin 7 → ℤ
  | 0 => 1
  | 1 => -1
  | 2 => -1
  | 3 => -1
  | 4 => 2
  | 5 => 0
  | 6 => 0

def splitDirection : Fin 7 → ℤ
  | 5 => 1
  | 6 => -1
  | _ => 0

/-- The rank-one perturbation of the constant transition table. -/
def transitionWeight (i j : Fin 7) : ℕ :=
  (2+splitDirection i*mergeDirection j).toNat

lemma transition_row_mass : ∀ i : Fin 7, ∑ j : Fin 7, transitionWeight i j = 14 := by
  decide +kernel

lemma transition_column_mass : ∀ j : Fin 7, ∑ i : Fin 7, transitionWeight i j = 14 := by
  decide +kernel

lemma transition_total_mass : (∑ i : Fin 7, ∑ j : Fin 7, transitionWeight i j) = 98 := by
  decide +kernel

lemma largest_rising_mass :
    (∑ i : Fin 7, ∑ j : Fin 7,
      if (largeParts i).sup id < (largeParts j).sup id then transitionWeight i j else 0) = 41 := by
  decide +kernel

lemma largest_falling_mass :
    (∑ i : Fin 7, ∑ j : Fin 7,
      if (largeParts j).sup id < (largeParts i).sup id then transitionWeight i j else 0) = 43 := by
  decide +kernel

lemma largest_tie_mass :
    (∑ i : Fin 7, ∑ j : Fin 7,
      if (largeParts i).sup id = (largeParts j).sup id then transitionWeight i j else 0) = 14 := by
  decide +kernel

def transitionPower : ℕ → Fin 7 → Fin 7 → ℕ
  | 0, i, j => if i = j then 1 else 0
  | k+1, i, j => ∑ l : Fin 7, transitionWeight i l*transitionPower k l j

lemma transitionPower_one (i j : Fin 7) : transitionPower 1 i j = transitionWeight i j := by
  simp [transitionPower]

lemma transitionPower_two : ∀ i j : Fin 7, transitionPower 2 i j = 28 := by
  decide +kernel

/-- After two steps the transition matrix is exactly uniform. Normalizing
by the row mass 14 therefore gives independence at every gap at least two. -/
lemma transitionPower_after_two (k : ℕ) (i j : Fin 7) :
    transitionPower (k+2) i j = 28*14^k := by
  induction k generalizing i j with
  | zero => simpa using transitionPower_two i j
  | succ k ih =>
    rw [show (k+1)+2=(k+2)+1 by omega,transitionPower]
    simp_rw [ih]
    rw [← sum_mul,transition_row_mass]
    ring

def observationClass (s : Finset ℕ) (U : Finset Bool) : Finset (Fin 7) :=
  univ.filter fun i => s ⊆ largeParts i ∧ tailType i ∈ U

def gapMoment (k : ℕ) (s t : Finset ℕ) (U V : Finset Bool) : ℕ :=
  ∑ i ∈ observationClass s U, ∑ j ∈ observationClass t V, transitionPower k i j

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma small_moment_factors_finite :
    ∀ s ∈ observations, ∀ t ∈ observations, ∀ U V : Finset Bool,
      (∑ a ∈ s, a)+(∑ b ∈ t, b) ≤ 966 →
        gapMoment 1 s t U V = 2*(observationClass s U).card*(observationClass t V).card := by
  decide +kernel

lemma observationClass_empty (s : Finset ℕ) (U : Finset Bool) (hs : s ∉ observations) :
    observationClass s U = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro i hi
  have hsub := (mem_filter.mp hi).2.1
  exact hs ((mem_observations_iff s).mpr ⟨i,hsub⟩)

lemma small_moment_factors (s t : Finset ℕ) (U V : Finset Bool)
    (h : (∑ a ∈ s, a)+(∑ b ∈ t, b) ≤ 966) :
    gapMoment 1 s t U V = 2*(observationClass s U).card*(observationClass t V).card := by
  by_cases hs : s ∈ observations
  · by_cases ht : t ∈ observations
    · exact small_moment_factors_finite s hs t ht U V h
    · simp [gapMoment,observationClass_empty t V ht]
  · simp [gapMoment,observationClass_empty s U hs]

lemma all_moments_factor_after_two (k : ℕ) (s t : Finset ℕ) (U V : Finset Bool) :
    gapMoment (k+2) s t U V = (28*14^k)*(observationClass s U).card*(observationClass t V).card := by
  unfold gapMoment
  simp_rw [transitionPower_after_two]
  simp only [sum_const,nsmul_eq_mul, Nat.cast_id]
  ring

/-- Low-mass inclusion moments, even with arbitrary tail-type conditioning,
factor at every positive gap. The factor accounts for unnormalized path
weights: the total k+1-step mass is 7*14^(k+1). -/
theorem small_moments_factor_all_gaps (k : ℕ) (s t : Finset ℕ) (U V : Finset Bool)
    (h : (∑ a ∈ s, a)+(∑ b ∈ t, b) ≤ 966) :
    gapMoment (k+1) s t U V = (2*14^k)*(observationClass s U).card*(observationClass t V).card := by
  cases k with
  | zero => simpa using small_moment_factors s t U V h
  | succ k =>
    rw [show (k+1)+1=k+2 by omega,all_moments_factor_after_two]
    ring

/-- Despite stationarity and all the preceding low-moment identities, the
largest-label comparison is not balanced at gap one. -/
theorem largest_comparison_biased :
    (∑ i : Fin 7, ∑ j : Fin 7,
      if (largeParts i).sup id < (largeParts j).sup id then transitionWeight i j else 0) ≠
    (∑ i : Fin 7, ∑ j : Fin 7,
      if (largeParts j).sup id < (largeParts i).sup id then transitionWeight i j else 0) := by
  rw [largest_rising_mass,largest_falling_mass]
  decide

#print axioms transitionPower_after_two
#print axioms small_moments_factor_all_gaps
#print axioms largest_comparison_biased
end Erdos371.StationaryMomentObstruction
