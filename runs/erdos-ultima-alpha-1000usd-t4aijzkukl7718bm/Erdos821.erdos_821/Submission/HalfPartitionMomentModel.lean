import FormalConjecturesUtil

/-!
# A half-level partition moment model without fourth-root-smooth outcomes

An exact finite model on partitions of 12. All joint binomial moments of
selected total size at most 6 match the permutation-factor model, INCLUDING
the half-size endpoint. Every single-part mean is exactly 1/j as well.
Nevertheless every outcome has a part at least 4, so none is fourth-root
smooth. This is only a finite moment-inference certificate: it is not a model
of primes, an asymptotic construction, or a disproof of Erdos 821.

All certificate checks use kernel-verified exact arithmetic.
-/

namespace Erdos821.HalfPartitionMomentModel

set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

def data : List (List ℕ × ℕ) :=
  [
    ([12], 37398271680),
    ([11, 1], 40798114560),
    ([10, 2], 30480368688),
    ([10, 1, 1], 14397557328),
    ([9, 3], 28544234208),
    ([9, 2, 1], 15230898144),
    ([9, 1, 1, 1], 6089229888),
    ([8, 2, 2], 12552339828),
    ([8, 2, 1, 1], 38530459800),
    ([8, 1, 1, 1, 1], 5014607892),
    ([7, 5], 2949842112),
    ([7, 4, 1], 51574683744),
    ([7, 3, 1, 1], 9586797024),
    ([6, 6], 15745267104),
    ([6, 3, 3], 5202024912),
    ([6, 3, 2, 1], 25752436416),
    ([6, 3, 1, 1, 1], 12050290560),
    ([6, 1, 1, 1, 1, 1, 1], 301257264),
    ([5, 5, 2], 14978675376),
    ([5, 5, 1, 1], 17788218000),
    ([5, 3, 3, 1], 14310907296),
    ([5, 3, 2, 2], 2669243136),
    ([5, 2, 2, 2, 1], 4292072736),
    ([4, 4, 4], 8953011312),
    ([4, 4, 1, 1, 1, 1], 172646208),
    ([4, 3, 3, 2], 5138289184),
    ([4, 3, 3, 1, 1], 280959728),
    ([4, 3, 2, 2, 1], 12810754992),
    ([4, 3, 2, 1, 1, 1], 7807532320),
    ([4, 3, 1, 1, 1, 1, 1], 507435824),
    ([4, 2, 2, 2, 2], 532417641),
    ([4, 2, 2, 2, 1, 1], 2927824620),
    ([4, 2, 2, 1, 1, 1, 1], 3210871650),
    ([4, 2, 1, 1, 1, 1, 1, 1], 195188308),
    ([4, 1, 1, 1, 1, 1, 1, 1, 1], 4530677)
  ]

def totalMass : ℕ := 448779260160

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

end Erdos821.HalfPartitionMomentModel
