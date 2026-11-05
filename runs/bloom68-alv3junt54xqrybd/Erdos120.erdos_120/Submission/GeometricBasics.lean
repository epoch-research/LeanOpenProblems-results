import FormalConjecturesUtil
import Submission.Reductions

/-!
# Basic infrastructure for the geometric sequence

`GeometricSet` contains the powers `(1 / 2)^n` for natural indices starting at
zero. It is bounded and infinite, contains `1`, and does not contain its limit
`0`. Adjoining that limit gives its compact closure.

Every tail is a nonzero rescaling of the whole set. In particular, an affine
copy of a tail inside a target can be rescaled to an affine copy of the whole
set inside the same target. The positive-index version `2^(-n)`, `n ≥ 1`, is
also a nonzero rescaling.

The final avoidance equivalence is only a classical logical reformulation.
Neither `¬ Avoidance GeometricSet` nor a uniform positive volume bound is proved
here. This file is independent of `Submission.Spec` and the original conjecture.
-/

open Set MeasureTheory Filter
open scoped Topology

namespace Erdos120Aux

/-- The geometric sequence indexed from zero; its first point is `1`, not `0`. -/
def GeometricSet : Set ℝ := Set.range (fun n : ℕ => (1 / 2 : ℝ) ^ n)

/-- Every power in the sequence is strictly positive. -/
theorem geometric_pow_pos (n : ℕ) : 0 < (1 / 2 : ℝ) ^ n :=
  pow_pos (by norm_num) n

/-- The scale used to identify any tail with the whole sequence is nonzero. -/
theorem geometric_pow_ne_zero (n : ℕ) : (1 / 2 : ℝ) ^ n ≠ 0 :=
  ne_of_gt (geometric_pow_pos n)

/-- Strict decrease follows from `0 < 1 / 2 < 1`. -/
theorem geometric_pow_strictAnti : StrictAnti (fun n : ℕ => (1 / 2 : ℝ) ^ n) :=
  pow_right_strictAnti₀ (by norm_num) (by norm_num)

/-- Each term belongs to the geometric set. -/
theorem geometric_pow_mem_GeometricSet (n : ℕ) : (1 / 2 : ℝ) ^ n ∈ GeometricSet :=
  Set.mem_range_self n

/-- The zero-indexed geometric set contains `1`. -/
theorem one_mem_GeometricSet : (1 : ℝ) ∈ GeometricSet := by
  exact ⟨0, by simp⟩

/-- Strict decrease makes the natural-indexed sequence injective, hence infinite. -/
theorem GeometricSet_infinite : GeometricSet.Infinite :=
  Set.infinite_range_of_injective geometric_pow_strictAnti.injective

/-- All points of the geometric set are positive. -/
theorem pos_of_mem_GeometricSet {x : ℝ} (hx : x ∈ GeometricSet) : 0 < x := by
  obtain ⟨n, rfl⟩ := hx
  exact geometric_pow_pos n

/-- The limit `0` is not a point of the geometric set. -/
theorem zero_not_mem_GeometricSet : (0 : ℝ) ∉ GeometricSet := by
  intro h
  exact (lt_irrefl (0 : ℝ)) (pos_of_mem_GeometricSet h)

/-- The geometric set lies in the closed unit interval. -/
theorem GeometricSet_subset_Icc : GeometricSet ⊆ Set.Icc (0 : ℝ) 1 := by
  rintro x ⟨n, rfl⟩
  refine ⟨(geometric_pow_pos n).le, ?_⟩
  simpa only [pow_zero] using geometric_pow_strictAnti.antitone (Nat.zero_le n)

/-- In particular, the geometric set is bounded. -/
theorem GeometricSet_isBounded : Bornology.IsBounded GeometricSet :=
  (Metric.isBounded_Icc (0 : ℝ) 1).subset GeometricSet_subset_Icc

/-- The geometric sequence converges to `0`. -/
theorem geometric_pow_tendsto_zero :
    Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 (0 : ℝ)) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

/-- A convergent sequence together with its limit is compact. -/
theorem isCompact_insert_zero_GeometricSet : IsCompact (insert (0 : ℝ) GeometricSet) :=
  geometric_pow_tendsto_zero.isCompact_insert_range

/-- Although absent from the sequence, `0` belongs to its closure. -/
theorem zero_mem_closure_GeometricSet : (0 : ℝ) ∈ closure GeometricSet :=
  mem_closure_of_tendsto geometric_pow_tendsto_zero
    (Eventually.of_forall geometric_pow_mem_GeometricSet)

/-- Adjoining `0` accounts for the entire closure. -/
theorem closure_GeometricSet : closure GeometricSet = insert (0 : ℝ) GeometricSet := by
  apply Set.Subset.antisymm
  · exact closure_minimal (Set.subset_insert _ _) isCompact_insert_zero_GeometricSet.isClosed
  · exact Set.insert_subset zero_mem_closure_GeometricSet subset_closure

/-- Tail self-similarity, with the scale explicitly equal to `(1 / 2)^N`.
The scale is nonzero by `geometric_pow_ne_zero N`. -/
theorem geometric_tail_eq_image (N : ℕ) :
    Set.range (fun n : ℕ => (1 / 2 : ℝ) ^ (N + n)) =
      Set.image (fun x : ℝ => (1 / 2 : ℝ) ^ N * x) GeometricSet := by
  simpa only [pow_add, GeometricSet] using
    (Set.range_comp' (fun x : ℝ => (1 / 2 : ℝ) ^ N * x)
      (fun n : ℕ => (1 / 2 : ℝ) ^ n))

/-- Avoidance of any tail is equivalent to avoidance of the whole geometric set. -/
theorem avoidance_geometric_tail_iff (N : ℕ) :
    Avoidance (Set.range (fun n : ℕ => (1 / 2 : ℝ) ^ (N + n))) ↔
      Avoidance GeometricSet := by
  rw [geometric_tail_eq_image N]
  simpa only [add_zero] using
    (avoidance_affine_image_iff (A := GeometricSet) (geometric_pow_ne_zero N) (0 : ℝ))

/-- The positive-index convention `2^(-n)`, `n ≥ 1`, is the half-scaled
zero-indexed set. The exponent on `2` is an integer. -/
theorem geometric_positive_index_eq_image :
    {x : ℝ | ∃ n : ℕ, 1 ≤ n ∧ (2 : ℝ) ^ (-(n : ℤ)) = x} =
      Set.image (fun x : ℝ => (1 / 2 : ℝ) * x) GeometricSet := by
  have hpow (n : ℕ) : (2 : ℝ) ^ (-(n : ℤ)) = (1 / 2 : ℝ) ^ n := by
    simp [zpow_neg, one_div, inv_pow]
  calc
    {x : ℝ | ∃ n : ℕ, 1 ≤ n ∧ (2 : ℝ) ^ (-(n : ℤ)) = x} =
        Set.range (fun n : ℕ => (1 / 2 : ℝ) ^ (1 + n)) := by
      ext x
      constructor
      · rintro ⟨n, hn, rfl⟩
        obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
        exact ⟨m, (hpow (1 + m)).symm⟩
      · rintro ⟨n, rfl⟩
        exact ⟨1 + n, Nat.le_add_right 1 n, hpow (1 + n)⟩
    _ = Set.image (fun x : ℝ => (1 / 2 : ℝ) * x) GeometricSet := by
      simpa only [pow_one] using geometric_tail_eq_image 1

/-- Rescaling a nonzero affine slope by a tail scale keeps it nonzero. -/
theorem geometric_tail_affine_scale_ne_zero {a : ℝ} (ha : a ≠ 0) (N : ℕ) :
    a * (1 / 2 : ℝ) ^ N ≠ 0 :=
  mul_ne_zero ha (geometric_pow_ne_zero N)

/-- Containment of an affine tail yields containment of the whole geometric set
with the explicit new slope `a * (1 / 2)^N` and the same translation `b`. -/
theorem geometric_affine_image_subset_of_tail {E : Set ℝ} {a b : ℝ} (N : ℕ)
    (htail : ∀ n : ℕ, N ≤ n → a * (1 / 2 : ℝ) ^ n + b ∈ E) :
    Set.image (fun x : ℝ => (a * (1 / 2 : ℝ) ^ N) * x + b) GeometricSet ⊆ E := by
  rintro y ⟨x, ⟨n, rfl⟩, rfl⟩
  simpa only [pow_add, mul_assoc] using htail (N + n) (Nat.le_add_right N n)

/-- An existential nonzero affine copy of a tail produces a nonzero affine copy
of the whole set. No measurability or measure hypothesis on the target is needed. -/
theorem exists_affine_image_GeometricSet_subset_of_tail {E : Set ℝ} {N : ℕ}
    (h : ∃ a b : ℝ, a ≠ 0 ∧ ∀ n : ℕ, N ≤ n → a * (1 / 2 : ℝ) ^ n + b ∈ E) :
    ∃ a' b : ℝ, a' ≠ 0 ∧ Set.image (fun x : ℝ => a' * x + b) GeometricSet ⊆ E := by
  obtain ⟨a, b, ha, htail⟩ := h
  exact ⟨a * (1 / 2 : ℝ) ^ N, b, geometric_tail_affine_scale_ne_zero ha N,
    geometric_affine_image_subset_of_tail N htail⟩

/-- Classical negation of the avoidance quantifiers, for any source set.
This equivalence does not assert either side for a particular source set. -/
theorem not_avoidance_iff_forall_exists_affine_image {A : Set ℝ} :
    ¬ Avoidance A ↔ ∀ E : Set ℝ, MeasurableSet E → 0 < volume E →
      ∃ a b : ℝ, a ≠ 0 ∧ Set.image (fun x : ℝ => a * x + b) A ⊆ E := by
  classical
  unfold Avoidance
  push_neg
  rfl

/-- Merely a logical reformulation of the still-unproved geometric non-avoidance
claim: every measurable positive-volume target would contain a nonzero affine copy. -/
theorem not_avoidance_GeometricSet_iff :
    ¬ Avoidance GeometricSet ↔ ∀ E : Set ℝ, MeasurableSet E → 0 < volume E →
      ∃ a b : ℝ, a ≠ 0 ∧ Set.image (fun x : ℝ => a * x + b) GeometricSet ⊆ E :=
  not_avoidance_iff_forall_exists_affine_image

end Erdos120Aux
