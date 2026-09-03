import FormalConjecturesUtil

/-!
# An exact finite partition model with no cube-root-smooth outcome

This is a finite moment-inference test, not a model asserted to represent primes.
Every outcome is a partition of 12 with a part at least 5. The distribution
matches all single-part means 1/j, and every binomial moment of selected total
size at most 5. Thus those finite data, even together with the exact total-size
constraint, do not by themselves force a cube-root-smooth outcome.

The rational certificate below is checked by the Lean kernel. No external
solver is used in any proof, and no asymptotic countermodel is asserted.
-/

namespace Erdos821.PartitionMomentModel

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

/-- Each pair consists of a partition and its positive integer mass. -/
def data : List (List ℕ × ℕ) :=
  [
    ([12], 94710),
    ([11, 1], 103320),
    ([10, 2], 72296),
    ([10, 1, 1], 41356),
    ([9, 2, 1], 126280),
    ([8, 4], 101878),
    ([8, 3, 1], 27062),
    ([8, 1, 1, 1, 1], 13125),
    ([7, 4, 1], 85694),
    ([7, 3, 2], 76666),
    ([6, 6], 6940),
    ([6, 4, 1, 1], 91238),
    ([6, 3, 3], 34751),
    ([6, 3, 1, 1, 1], 26250),
    ([6, 2, 2, 2], 7516),
    ([6, 2, 1, 1, 1, 1], 15785),
    ([5, 5, 2], 15651),
    ([5, 4, 1, 1, 1], 5320),
    ([5, 3, 3, 1], 36484),
    ([5, 3, 2, 2], 9022),
    ([5, 3, 2, 1, 1], 94710),
    ([5, 3, 1, 1, 1, 1], 2660),
    ([5, 2, 2, 2, 1], 31570),
    ([5, 2, 2, 1, 1, 1], 15785),
    ([5, 1, 1, 1, 1, 1, 1, 1], 451)
  ]

def totalMass : ℕ := 1136520

def weightedSum (L : List (List ℕ × ℕ)) (f : List ℕ → ℕ) : ℕ :=
  (L.map fun r => r.2 * f r.1).sum

def moment (a b c d e : ℕ) (p : List ℕ) : ℕ :=
  (p.count 1).choose a * (p.count 2).choose b * (p.count 3).choose c *
    (p.count 4).choose d * (p.count 5).choose e

def momentDenominator (a b c d e : ℕ) : ℕ :=
  a.factorial * (2^b * b.factorial) * (3^c * c.factorial) *
    (4^d * d.factorial) * (5^e * e.factorial)

/-- Positivity, total size, and a factor strictly above the cube-root threshold
hold at every outcome, not only in expectation. -/
theorem support_properties :
    ∀ r ∈ data, 0 < r.2 ∧ r.1.sum = 12 ∧
      (∀ j ∈ r.1, 0 < j) ∧ ∃ j ∈ r.1, 5 ≤ j := by
  decide

theorem normalized_mass : weightedSum data (fun _ => 1) = totalMass := by
  decide

/-- All single-part moments are exact, even above the truncated joint level. -/
theorem single_part_moment (j : ℕ) (hj : 1 ≤ j) (hj' : j ≤ 12) :
    j * weightedSum data (fun p => p.count j) = totalMass := by
  interval_cases j <;> decide

/-- Exact binomial moments for every selection of total size at most five. -/
theorem low_weight_moments (a b c d e : ℕ)
    (h : a + 2*b + 3*c + 4*d + 5*e ≤ 5) :
    weightedSum data (moment a b c d e) * momentDenominator a b c d e = totalMass := by
  have checked : ∀ a : Fin 6, ∀ b : Fin 3, ∀ c d e : Fin 2,
      a.val + 2*b.val + 3*c.val + 4*d.val + 5*e.val ≤ 5 →
      weightedSum data (moment a.val b.val c.val d.val e.val) *
        momentDenominator a.val b.val c.val d.val e.val = totalMass := by
    decide
  exact checked ⟨a, by omega⟩ ⟨b, by omega⟩ ⟨c, by omega⟩
    ⟨d, by omega⟩ ⟨e, by omega⟩ h

/-- There is no mass at any outcome all of whose parts are at most one third
of its total size. -/
theorem cube_root_smooth_mass_zero :
    weightedSum data (fun p => if ∀ j ∈ p, 3*j ≤ p.sum then 1 else 0) = 0 := by
  decide

/-- The normalized rational expectation of a natural-valued statistic. -/
def mean (f : List ℕ → ℕ) : ℚ := (weightedSum data f : ℚ) / (totalMass : ℚ)

theorem mean_one : mean (fun _ => 1) = 1 := by
  unfold mean
  rw [normalized_mass]
  norm_num [totalMass]

theorem mean_count (j : ℕ) (hj : 1 ≤ j) (hj' : j ≤ 12) :
    mean (fun p => p.count j) = (j : ℚ)⁻¹ := by
  have hj0 : (j : ℚ) ≠ 0 := by exact_mod_cast (show j ≠ 0 by omega)
  have ht : (totalMass : ℚ) ≠ 0 := by norm_num [totalMass]
  have H : (j : ℚ) * (weightedSum data (fun p => p.count j) : ℚ) =
      (totalMass : ℚ) := by exact_mod_cast single_part_moment j hj hj'
  unfold mean
  field_simp
  nlinarith [H]

theorem mean_low_weight_moment (a b c d e : ℕ)
    (h : a + 2*b + 3*c + 4*d + 5*e ≤ 5) :
    mean (moment a b c d e) = (momentDenominator a b c d e : ℚ)⁻¹ := by
  have hd : 0 < momentDenominator a b c d e := by
    unfold momentDenominator
    positivity
  have hd0 : (momentDenominator a b c d e : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have ht : (totalMass : ℚ) ≠ 0 := by norm_num [totalMass]
  have H : (weightedSum data (moment a b c d e) : ℚ) *
      (momentDenominator a b c d e : ℚ) = (totalMass : ℚ) := by
    exact_mod_cast low_weight_moments a b c d e h
  unfold mean
  field_simp
  exact H

theorem mean_cube_root_smooth_zero :
    mean (fun p => if ∀ j ∈ p, 3*j ≤ p.sum then 1 else 0) = 0 := by
  unfold mean
  rw [cube_root_smooth_mass_zero]
  norm_num

end Erdos821.PartitionMomentModel
