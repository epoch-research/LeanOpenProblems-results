import Submission.PartitionObstruction

/-!
The finite partition obstruction persists after conditioning on all information
that depends only on its two tail types. This is not an arithmetic counterexample.
-/

namespace Erdos371.RefinedPartitionObstruction

open PartitionObstructionWithSmallParts (weight)

def largeParts : Fin 7 → Finset ℕ
  | 0 => {240, 300, 360}
  | 1 => {240, 660}
  | 2 => {300, 600}
  | 3 => {360, 540}
  | 4 => {900}
  | 5 => {427, 488}
  | 6 => {915}

def tailType (i : Fin 7) : Bool := decide (5 ≤ i.val)

def observations : Finset (Finset ℕ) :=
  Finset.univ.biUnion (fun i : Fin 7 => (largeParts i).powerset)

/-- `u` and `v` encode arbitrary information about the respective tail types. -/
def moment (s t : Finset ℕ) (u v : Finset Bool) : ℕ :=
  ∑ i : Fin 7, ∑ j : Fin 7,
    if s ⊆ largeParts i ∧ t ⊆ largeParts j ∧ tailType i ∈ u ∧ tailType j ∈ v
    then weight i j else 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma small_moment_symmetry_finite :
    ∀ s ∈ observations, ∀ t ∈ observations, ∀ u v : Finset Bool,
      (∑ a ∈ s, a) + (∑ b ∈ t, b) ≤ 966 → moment s t u v = moment t s v u := by
  decide +kernel

lemma mem_observations_iff (s : Finset ℕ) :
    s ∈ observations ↔ ∃ i : Fin 7, s ⊆ largeParts i := by
  simp [observations]

lemma moment_eq_zero_left (s t : Finset ℕ) (u v : Finset Bool) (hs : s ∉ observations) :
    moment s t u v = 0 := by
  have h (i : Fin 7) : ¬ s ⊆ largeParts i := by
    intro hsub
    exact hs ((mem_observations_iff s).mpr ⟨i, hsub⟩)
  simp [moment, h]

lemma moment_eq_zero_right (s t : Finset ℕ) (u v : Finset Bool) (ht : t ∉ observations) :
    moment s t u v = 0 := by
  have h (i : Fin 7) : ¬ t ⊆ largeParts i := by
    intro hsub
    exact ht ((mem_observations_iff t).mpr ⟨i, hsub⟩)
  simp [moment, h]

/-- All low-mass moments remain symmetric even with arbitrary tail-type
conditions on both coordinates. In particular the original mass budget 945
cannot detect the asymmetry by refining those tails. -/
theorem small_moment_symmetry (s t : Finset ℕ) (u v : Finset Bool)
    (h : (∑ a ∈ s, a) + (∑ b ∈ t, b) ≤ 966) : moment s t u v = moment t s v u := by
  by_cases hs : s ∈ observations
  · by_cases ht : t ∈ observations
    · exact small_moment_symmetry_finite s hs t ht u v h
    · rw [moment_eq_zero_right s t u v ht, moment_eq_zero_left t s v u ht]
  · rw [moment_eq_zero_left s t u v hs, moment_eq_zero_right t s v u hs]

/-- The budget 966 is sharp for this model. -/
theorem first_asymmetric_moment :
    (∑ a ∈ ({240, 300} : Finset ℕ), a) + (∑ b ∈ ({427} : Finset ℕ), b) = 967 ∧
      moment {240, 300} {427} {false} {true} = 0 ∧
      moment {427} {240, 300} {true} {false} = 1 := by
  decide +kernel

theorem largest_comparison_still_asymmetric :
    (∑ i : Fin 7, ∑ j : Fin 7,
      if (largeParts i).sup id < (largeParts j).sup id then weight i j else 0) = 5 ∧
    (∑ i : Fin 7, ∑ j : Fin 7,
      if (largeParts j).sup id < (largeParts i).sup id then weight i j else 0) = 7 := by
  decide +kernel

#print axioms small_moment_symmetry
#print axioms first_asymmetric_moment
#print axioms largest_comparison_still_asymmetric

end Erdos371.RefinedPartitionObstruction
