import FormalConjecturesUtil

/-!
# A half-level partition moment model without fourth-root-smooth outcomes

An exact finite model on partitions of 12. All joint binomial moments of
selected total size at most 6 match the permutation-factor model, INCLUDING
the half-size endpoint. Every single-part mean is exactly 1/j as well.
Every outcome has a part at least 4, so none is fourth-root smooth.
Additionally the candidate law is pointwise bounded by twice the finite
permutation reference law, hence satisfies all corresponding nonnegative
upper tests with factor two. This is only a finite moment-inference certificate: it is not a model
of primes, an asymptotic construction, or a disproof of Erdos 821.

All certificate checks use kernel-verified exact arithmetic.
-/

namespace Erdos821.DominatedHalfPartitionModel

set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

def data : List (List ℕ × ℕ) :=
  [
    ([12], 1108800),
    ([11, 1], 1209600),
    ([10, 2], 772936),
    ([10, 1, 1], 557624),
    ([9, 3], 444896),
    ([9, 2, 1], 589984),
    ([9, 1, 1, 1], 443520),
    ([8, 4], 786836),
    ([8, 3, 1], 286744),
    ([8, 2, 2], 196922),
    ([8, 2, 1, 1], 335040),
    ([8, 1, 1, 1, 1], 57658),
    ([7, 5], 336576),
    ([7, 4, 1], 745944),
    ([7, 3, 2], 330240),
    ([7, 3, 1, 1], 446944),
    ([7, 2, 2, 1], 41096),
    ([6, 5, 1], 415664),
    ([6, 4, 2], 77696),
    ([6, 4, 1, 1], 479888),
    ([6, 3, 3], 240752),
    ([6, 3, 2, 1], 530512),
    ([6, 3, 1, 1, 1], 73920),
    ([6, 2, 2, 2], 92400),
    ([6, 2, 2, 1, 1], 277200),
    ([6, 2, 1, 1, 1, 1], 27720),
    ([6, 1, 1, 1, 1, 1, 1], 1848),
    ([5, 5, 2], 266112),
    ([5, 4, 2, 1], 431824),
    ([5, 3, 3, 1], 295680),
    ([5, 3, 2, 1, 1], 330240),
    ([5, 3, 1, 1, 1, 1], 73920),
    ([5, 2, 2, 2, 1], 110880),
    ([5, 2, 2, 1, 1, 1], 110880),
    ([5, 2, 1, 1, 1, 1, 1], 22176),
    ([5, 1, 1, 1, 1, 1, 1, 1], 1056),
    ([4, 4, 2, 2], 38698),
    ([4, 4, 1, 1, 1, 1], 11642),
    ([4, 3, 3, 2], 184800),
    ([4, 3, 3, 1, 1], 17968),
    ([4, 3, 2, 2, 1], 236104),
    ([4, 3, 2, 1, 1, 1], 184800),
    ([4, 3, 1, 1, 1, 1, 1], 18480),
    ([4, 2, 2, 2, 2], 17325),
    ([4, 2, 2, 2, 1, 1], 4620),
    ([4, 2, 2, 1, 1, 1, 1], 34650),
    ([4, 2, 1, 1, 1, 1, 1, 1], 4620),
    ([4, 1, 1, 1, 1, 1, 1, 1, 1], 165)
  ]

def totalMass : ℕ := 13305600

def weightedSum (L : List (List ℕ × ℕ)) (f : List ℕ → ℕ) : ℕ :=
  (L.map fun r => r.2 * f r.1).sum

def moment (a b c d e f : ℕ) (p : List ℕ) : ℕ :=
  (p.count 1).choose a * (p.count 2).choose b * (p.count 3).choose c *
    (p.count 4).choose d * (p.count 5).choose e * (p.count 6).choose f

def momentDenominator (a b c d e f : ℕ) : ℕ :=
  a.factorial * (2^b * b.factorial) * (3^c * c.factorial) *
    (4^d * d.factorial) * (5^e * e.factorial) * (6^f * f.factorial)

theorem support_properties :
    ∀ r ∈ data, 0 < r.2 ∧ r.1.sum = 12 ∧
      (∀ j ∈ r.1, 0 < j) ∧ ∃ j ∈ r.1, 4 ≤ j := by
  decide

theorem normalized_mass : weightedSum data (fun _ => 1) = totalMass := by
  decide

theorem single_part_moment (j : ℕ) (hj : 1 ≤ j) (hj' : j ≤ 12) :
    j * weightedSum data (fun p => p.count j) = totalMass := by
  interval_cases j <;> decide

/-- The endpoint of half the total size is included. -/
theorem half_weight_moments (a b c d e f : ℕ)
    (h : a + 2*b + 3*c + 4*d + 5*e + 6*f ≤ 6) :
    weightedSum data (moment a b c d e f) * momentDenominator a b c d e f =
      totalMass := by
  have checked : ∀ a : Fin 7, ∀ b : Fin 4, ∀ c : Fin 3, ∀ d e f : Fin 2,
      a.val + 2*b.val + 3*c.val + 4*d.val + 5*e.val + 6*f.val ≤ 6 →
      weightedSum data (moment a.val b.val c.val d.val e.val f.val) *
        momentDenominator a.val b.val c.val d.val e.val f.val = totalMass := by
    decide
  exact checked ⟨a, by omega⟩ ⟨b, by omega⟩ ⟨c, by omega⟩
    ⟨d, by omega⟩ ⟨e, by omega⟩ ⟨f, by omega⟩ h

theorem fourth_root_smooth_mass_zero :
    weightedSum data (fun p => if ∀ j ∈ p, 4*j ≤ p.sum then 1 else 0) = 0 := by
  decide

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

theorem mean_half_weight_moment (a b c d e f : ℕ)
    (h : a + 2*b + 3*c + 4*d + 5*e + 6*f ≤ 6) :
    mean (moment a b c d e f) = (momentDenominator a b c d e f : ℚ)⁻¹ := by
  have hd : 0 < momentDenominator a b c d e f := by
    unfold momentDenominator
    positivity
  have hd0 : (momentDenominator a b c d e f : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have ht : (totalMass : ℚ) ≠ 0 := by norm_num [totalMass]
  have H : (weightedSum data (moment a b c d e f) : ℚ) *
      (momentDenominator a b c d e f : ℚ) = (totalMass : ℚ) := by
    exact_mod_cast half_weight_moments a b c d e f h
  unfold mean
  field_simp
  exact H

theorem mean_fourth_root_smooth_zero :
    mean (fun p => if ∀ j ∈ p, 4*j ≤ p.sum then 1 else 0) = 0 := by
  unfold mean
  rw [fourth_root_smooth_mass_zero]
  norm_num



/-- Denominator of the permutation cycle-type mass. -/
def cycleDenominator (p : List ℕ) : ℕ :=
  ((List.range 13).map fun j => j^(p.count j)*(p.count j).factorial).prod

def referencePartitions : List (List ℕ) :=
  [
    [12],
    [11, 1],
    [10, 2],
    [10, 1, 1],
    [9, 3],
    [9, 2, 1],
    [9, 1, 1, 1],
    [8, 4],
    [8, 3, 1],
    [8, 2, 2],
    [8, 2, 1, 1],
    [8, 1, 1, 1, 1],
    [7, 5],
    [7, 4, 1],
    [7, 3, 2],
    [7, 3, 1, 1],
    [7, 2, 2, 1],
    [7, 2, 1, 1, 1],
    [7, 1, 1, 1, 1, 1],
    [6, 6],
    [6, 5, 1],
    [6, 4, 2],
    [6, 4, 1, 1],
    [6, 3, 3],
    [6, 3, 2, 1],
    [6, 3, 1, 1, 1],
    [6, 2, 2, 2],
    [6, 2, 2, 1, 1],
    [6, 2, 1, 1, 1, 1],
    [6, 1, 1, 1, 1, 1, 1],
    [5, 5, 2],
    [5, 5, 1, 1],
    [5, 4, 3],
    [5, 4, 2, 1],
    [5, 4, 1, 1, 1],
    [5, 3, 3, 1],
    [5, 3, 2, 2],
    [5, 3, 2, 1, 1],
    [5, 3, 1, 1, 1, 1],
    [5, 2, 2, 2, 1],
    [5, 2, 2, 1, 1, 1],
    [5, 2, 1, 1, 1, 1, 1],
    [5, 1, 1, 1, 1, 1, 1, 1],
    [4, 4, 4],
    [4, 4, 3, 1],
    [4, 4, 2, 2],
    [4, 4, 2, 1, 1],
    [4, 4, 1, 1, 1, 1],
    [4, 3, 3, 2],
    [4, 3, 3, 1, 1],
    [4, 3, 2, 2, 1],
    [4, 3, 2, 1, 1, 1],
    [4, 3, 1, 1, 1, 1, 1],
    [4, 2, 2, 2, 2],
    [4, 2, 2, 2, 1, 1],
    [4, 2, 2, 1, 1, 1, 1],
    [4, 2, 1, 1, 1, 1, 1, 1],
    [4, 1, 1, 1, 1, 1, 1, 1, 1],
    [3, 3, 3, 3],
    [3, 3, 3, 2, 1],
    [3, 3, 3, 1, 1, 1],
    [3, 3, 2, 2, 2],
    [3, 3, 2, 2, 1, 1],
    [3, 3, 2, 1, 1, 1, 1],
    [3, 3, 1, 1, 1, 1, 1, 1],
    [3, 2, 2, 2, 2, 1],
    [3, 2, 2, 2, 1, 1, 1],
    [3, 2, 2, 1, 1, 1, 1, 1],
    [3, 2, 1, 1, 1, 1, 1, 1, 1],
    [3, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    [2, 2, 2, 2, 2, 2],
    [2, 2, 2, 2, 2, 1, 1],
    [2, 2, 2, 2, 1, 1, 1, 1],
    [2, 2, 2, 1, 1, 1, 1, 1, 1],
    [2, 2, 1, 1, 1, 1, 1, 1, 1, 1],
    [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
  ]

theorem reference_properties : referencePartitions.Nodup ∧
    ∀ p ∈ referencePartitions, p.sum = 12 ∧ ∀ j ∈ p, 0 < j := by
  decide

theorem support_sublist : (data.map Prod.fst).Sublist referencePartitions := by
  decide

theorem pointwise_reference_bound : ∀ r ∈ data,
    0 < cycleDenominator r.1 ∧
      r.2 * cycleDenominator r.1 ≤ 2 * totalMass := by
  decide

def meanQ (f : List ℕ → ℚ) : ℚ :=
  (data.map fun r => (r.2 : ℚ)/(totalMass : ℚ)*f r.1).sum

def referenceMeanQ (f : List ℕ → ℚ) : ℚ :=
  (referencePartitions.map fun p => f p/(cycleDenominator p : ℚ)).sum

theorem reference_normalized : referenceMeanQ (fun _ => 1) = 1 := by
  norm_num [referenceMeanQ, referencePartitions, cycleDenominator, List.range_succ]

/-- Every nonnegative statistic, not just a chosen finite list of tests,
obeys the factor-two upper bound. This concerns only the displayed finite
laws, not the actual distribution of prime predecessors. -/
theorem all_nonnegative_tests_bounded (f : List ℕ → ℚ)
    (hf : ∀ p ∈ referencePartitions, 0 ≤ f p) :
    meanQ f ≤ 2 * referenceMeanQ f := by
  have hT : (0 : ℚ) < totalMass := by norm_num [totalMass]
  have hpoint (r : List ℕ × ℕ) (hr : r ∈ data) :
      (r.2 : ℚ)/(totalMass : ℚ)*f r.1 ≤
        2*(f r.1/(cycleDenominator r.1 : ℚ)) := by
    have hd := pointwise_reference_bound r hr
    have hD : (0 : ℚ) < cycleDenominator r.1 := by exact_mod_cast hd.1
    have hw : (r.2 : ℚ)*(cycleDenominator r.1 : ℚ) ≤ 2*(totalMass : ℚ) := by
      exact_mod_cast hd.2
    have hratio : (r.2 : ℚ)/(totalMass : ℚ) ≤ 2/(cycleDenominator r.1 : ℚ) :=
      (div_le_div_iff₀ hT hD).mpr hw
    have hp : r.1 ∈ referencePartitions :=
      support_sublist.subset (List.mem_map_of_mem hr)
    calc
      _ ≤ (2/(cycleDenominator r.1 : ℚ))*f r.1 :=
        mul_le_mul_of_nonneg_right hratio (hf r.1 hp)
      _ = _ := by ring
  have hsum := (support_sublist.map
      (fun p => f p/(cycleDenominator p : ℚ))).sum_le_sum (by
    intro a ha
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp ha
    exact div_nonneg (hf p hp) (Nat.cast_nonneg _))
  simp only [List.map_map, Function.comp_def] at hsum
  calc
    meanQ f ≤ (data.map fun r => 2*(f r.1/(cycleDenominator r.1 : ℚ))).sum :=
      List.sum_le_sum hpoint
    _ = 2*(data.map fun r => f r.1/(cycleDenominator r.1 : ℚ)).sum :=
      List.sum_map_mul_left _ _ _
    _ ≤ 2*referenceMeanQ f := mul_le_mul_of_nonneg_left hsum (by norm_num)

lemma meanQ_nat (f : List ℕ → ℕ) :
    meanQ (fun p => (f p : ℚ)) = mean f := by
  calc
    _ = (data.map fun r => ((r.2 : ℚ)*(f r.1 : ℚ))*(totalMass : ℚ)⁻¹).sum := by
      unfold meanQ
      apply congrArg List.sum
      apply List.map_congr_left
      intro r _hr
      ring
    _ = (data.map fun r => (r.2 : ℚ)*(f r.1 : ℚ)).sum*(totalMass : ℚ)⁻¹ :=
      List.sum_map_mul_right _ _ _
    _ = mean f := by
      simp only [mean, weightedSum, Nat.cast_list_sum, List.map_map,
        Function.comp_def, Nat.cast_mul, div_eq_mul_inv]

theorem meanQ_count (j : ℕ) (hj : 1 ≤ j) (hj' : j ≤ 12) :
    meanQ (fun p => (p.count j : ℚ)) = (j : ℚ)⁻¹ := by
  rw [meanQ_nat]
  exact mean_count j hj hj'

theorem meanQ_half_weight_moment (a b c d e f : ℕ)
    (h : a + 2*b + 3*c + 4*d + 5*e + 6*f ≤ 6) :
    meanQ (fun p => (moment a b c d e f p : ℚ)) =
      (momentDenominator a b c d e f : ℚ)⁻¹ := by
  rw [meanQ_nat]
  exact mean_half_weight_moment a b c d e f h

theorem meanQ_one : meanQ (fun _ => 1) = 1 := by
  norm_num [meanQ, data, totalMass]

theorem meanQ_fourth_root_smooth_zero :
    meanQ (fun p => if ∀ j ∈ p, 4*j ≤ p.sum then 1 else 0) = 0 := by
  norm_num [meanQ, data, totalMass]

end Erdos821.DominatedHalfPartitionModel
