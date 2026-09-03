import FormalConjecturesUtil

/-! A tie-free obstruction to reconstructing comparison symmetry from
low-product inclusion moments alone. This is not a counterexample to Erdős 371. -/

namespace Erdos371.PartitionObstruction

/-- All six partitions have total mass fifteen. -/
def parts : Fin 6 → Finset ℕ
  | 0 => {4, 5, 6}
  | 1 => {4, 11}
  | 2 => {5, 10}
  | 3 => {6, 9}
  | 4 => {7, 8}
  | 5 => {15}

/-- Integer weights of a probability law, before division by ten. -/
def weight (i j : Fin 6) : ℕ :=
  if (i, j) ∈ ({(0, 5), (4, 0), (1, 4), (2, 4), (3, 4),
      (5, 1), (5, 2), (5, 3)} : Finset (Fin 6 × Fin 6)) then 1
  else if i = 4 ∧ j = 5 then 2 else 0

def largest (i : Fin 6) : ℕ := (parts i).sup id

def observations : Finset (Finset ℕ) :=
  Finset.univ.biUnion (fun i : Fin 6 => (parts i).powerset)

def moment (s t : Finset ℕ) : ℕ :=
  ∑ i : Fin 6, ∑ j : Fin 6, if s ⊆ parts i ∧ t ⊆ parts j then weight i j else 0

theorem mass_fifteen : ∀ i : Fin 6, ∑ a ∈ parts i, a = 15 := by
  decide +kernel

theorem total_weight : (∑ i : Fin 6, ∑ j : Fin 6, weight i j) = 10 := by
  decide +kernel

theorem equal_marginals :
    ∀ i : Fin 6, (∑ j : Fin 6, weight i j) = ∑ j : Fin 6, weight j i := by
  decide +kernel

theorem disjoint_support :
    ∀ i j : Fin 6, weight i j ≠ 0 → Disjoint (parts i) (parts j) := by
  decide +kernel

theorem no_largest_ties :
    ∀ i j : Fin 6, weight i j ≠ 0 → largest i ≠ largest j := by
  decide +kernel

theorem rising_weight :
    (∑ i : Fin 6, ∑ j : Fin 6, if largest i < largest j then weight i j else 0) = 3 := by
  decide +kernel

theorem falling_weight :
    (∑ i : Fin 6, ∑ j : Fin 6, if largest j < largest i then weight i j else 0) = 7 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma small_moment_symmetry_finite :
    ∀ s ∈ observations, ∀ t ∈ observations,
      (∑ a ∈ s, a) + (∑ b ∈ t, b) ≤ 15 → moment s t = moment t s := by
  decide +kernel

lemma mem_observations_iff (s : Finset ℕ) :
    s ∈ observations ↔ ∃ i : Fin 6, s ⊆ parts i := by
  simp [observations]

lemma moment_eq_zero_left (s t : Finset ℕ) (hs : s ∉ observations) :
    moment s t = 0 := by
  have h (i : Fin 6) : ¬ s ⊆ parts i := by
    intro hsub
    exact hs ((mem_observations_iff s).mpr ⟨i, hsub⟩)
  simp [moment, h]

lemma moment_eq_zero_right (s t : Finset ℕ) (ht : t ∉ observations) :
    moment s t = 0 := by
  have h (i : Fin 6) : ¬ t ⊆ parts i := by
    intro hsub
    exact ht ((mem_observations_iff t).mpr ⟨i, hsub⟩)
  simp [moment, h]

/-- All inclusion moments whose total observed mass is at most the total
mass of one partition are symmetric under swapping the two partitions. -/
theorem small_moment_symmetry (s t : Finset ℕ)
    (h : (∑ a ∈ s, a) + (∑ b ∈ t, b) ≤ 15) : moment s t = moment t s := by
  by_cases hs : s ∈ observations
  · by_cases ht : t ∈ observations
    · exact small_moment_symmetry_finite s hs t ht h
    · rw [moment_eq_zero_right s t ht, moment_eq_zero_left t s ht]
  · rw [moment_eq_zero_left s t hs, moment_eq_zero_right t s hs]

/-- Nevertheless the largest-part comparison is not symmetric. -/
theorem largest_comparison_not_symmetric :
    (∑ i : Fin 6, ∑ j : Fin 6, if largest i < largest j then weight i j else 0) ≠
      ∑ i : Fin 6, ∑ j : Fin 6, if largest j < largest i then weight i j else 0 := by
  rw [rising_weight, falling_weight]
  decide

#print axioms small_moment_symmetry
#print axioms largest_comparison_not_symmetric

end Erdos371.PartitionObstruction


namespace Erdos371.PartitionObstructionWithSmallParts

/-- Every partition has mass 945 and at least three parts. -/
def parts : Fin 7 → Finset ℕ
  | 0 => {240, 300, 360, 15, 30}
  | 1 => {240, 660, 15, 30}
  | 2 => {300, 600, 15, 30}
  | 3 => {360, 540, 15, 30}
  | 4 => {900, 15, 30}
  | 5 => {427, 488, 10, 20}
  | 6 => {915, 10, 20}

def weight (i j : Fin 7) : ℕ :=
  if (i, j) ∈ ({(0, 6), (5, 0), (1, 5), (2, 5), (3, 5),
      (6, 1), (6, 2), (6, 3)} : Finset (Fin 7 × Fin 7)) then 1
  else if (i, j) ∈ ({(5, 4), (4, 6)} : Finset (Fin 7 × Fin 7)) then 2 else 0

def largest (i : Fin 7) : ℕ := (parts i).sup id

def observations : Finset (Finset ℕ) :=
  Finset.univ.biUnion (fun i : Fin 7 => (parts i).powerset)

def moment (s t : Finset ℕ) : ℕ :=
  ∑ i : Fin 7, ∑ j : Fin 7, if s ⊆ parts i ∧ t ⊆ parts j then weight i j else 0

theorem mass_fixed : ∀ i : Fin 7, ∑ a ∈ parts i, a = 945 := by
  decide +kernel

theorem no_singleton_partitions : ∀ i : Fin 7, 3 ≤ (parts i).card := by
  decide +kernel

theorem largest_lt_total : ∀ i : Fin 7, largest i < 945 := by
  decide +kernel

theorem total_weight : (∑ i : Fin 7, ∑ j : Fin 7, weight i j) = 12 := by
  decide +kernel

theorem equal_marginals :
    ∀ i : Fin 7, (∑ j : Fin 7, weight i j) = ∑ j : Fin 7, weight j i := by
  decide +kernel

theorem disjoint_support :
    ∀ i j : Fin 7, weight i j ≠ 0 → Disjoint (parts i) (parts j) := by
  decide +kernel

theorem no_largest_ties :
    ∀ i j : Fin 7, weight i j ≠ 0 → largest i ≠ largest j := by
  decide +kernel

theorem rising_weight :
    (∑ i : Fin 7, ∑ j : Fin 7, if largest i < largest j then weight i j else 0) = 5 := by
  decide +kernel

theorem falling_weight :
    (∑ i : Fin 7, ∑ j : Fin 7, if largest j < largest i then weight i j else 0) = 7 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma small_moment_symmetry_finite :
    ∀ s ∈ observations, ∀ t ∈ observations,
      (∑ a ∈ s, a) + (∑ b ∈ t, b) ≤ 945 → moment s t = moment t s := by
  decide +kernel

lemma mem_observations_iff (s : Finset ℕ) :
    s ∈ observations ↔ ∃ i : Fin 7, s ⊆ parts i := by
  simp [observations]

lemma moment_eq_zero_left (s t : Finset ℕ) (hs : s ∉ observations) :
    moment s t = 0 := by
  have h (i : Fin 7) : ¬ s ⊆ parts i := by
    intro hsub
    exact hs ((mem_observations_iff s).mpr ⟨i, hsub⟩)
  simp [moment, h]

lemma moment_eq_zero_right (s t : Finset ℕ) (ht : t ∉ observations) :
    moment s t = 0 := by
  have h (i : Fin 7) : ¬ t ⊆ parts i := by
    intro hsub
    exact ht ((mem_observations_iff t).mpr ⟨i, hsub⟩)
  simp [moment, h]

theorem small_moment_symmetry (s t : Finset ℕ)
    (h : (∑ a ∈ s, a) + (∑ b ∈ t, b) ≤ 945) : moment s t = moment t s := by
  by_cases hs : s ∈ observations
  · by_cases ht : t ∈ observations
    · exact small_moment_symmetry_finite s hs t ht h
    · rw [moment_eq_zero_right s t ht, moment_eq_zero_left t s ht]
  · rw [moment_eq_zero_left s t hs, moment_eq_zero_right t s hs]

theorem largest_comparison_not_symmetric :
    (∑ i : Fin 7, ∑ j : Fin 7, if largest i < largest j then weight i j else 0) ≠
      ∑ i : Fin 7, ∑ j : Fin 7, if largest j < largest i then weight i j else 0 := by
  rw [rising_weight, falling_weight]
  decide

#print axioms small_moment_symmetry
#print axioms largest_comparison_not_symmetric

end Erdos371.PartitionObstructionWithSmallParts
