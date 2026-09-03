import Mathlib

/-!
# Finite occupancy and Bonferroni bounds

For a finite target set `t` and occupancies `n : β → ℕ`, `binomialMoment t n r`
is the sum of `Nat.choose (n b) r`. The real-valued `bonferroniSum t n k` is
its alternating sum through order `k`, starting at order one. Even truncations
bound the number of occupied targets from below; odd truncations bound it
from above.

The proofs use a pointwise truncated binomial identity, including zero
occupancies and truncation order zero. The final section specializes to
fibers of a map on a finite source. No finiteness assumption on the whole
source or target type, or on unrestricted fibers, is needed.

This is a finite combinatorial foundation only, not a proof of any factorial
support limit or asymptotic statement.
-/

open scoped BigOperators

noncomputable section

namespace OccupancyBounds

variable {β : Type*}

/-- Number of targets in `t` with positive occupancy. -/
def occupied (t : Finset β) (n : β → ℕ) : ℕ :=
  (t.filter fun b => 0 < n b).card

/-- The unnormalized binomial moment `S_r = ∑ b ∈ t, (n b).choose r`. -/
def binomialMoment (t : Finset β) (n : β → ℕ) (r : ℕ) : ℕ :=
  ∑ b ∈ t, (n b).choose r

/-- Pointwise alternating sum through order `k`, indexed from zero. -/
def truncatedBinomial (n k : ℕ) : ℝ :=
  ∑ r ∈ Finset.range k, (-1 : ℝ) ^ r * (n.choose (r + 1) : ℝ)

/-- Alternating binomial-moment sum through order `k`.
`bonferroniSum_eq_Icc` expresses this as a sum over `1 ≤ r ≤ k`. -/
def bonferroniSum (t : Finset β) (n : β → ℕ) (k : ℕ) : ℝ :=
  ∑ r ∈ Finset.range k, (-1 : ℝ) ^ r * (binomialMoment t n (r + 1) : ℝ)

@[simp]
theorem binomialMoment_zero (t : Finset β) (n : β → ℕ) :
    binomialMoment t n 0 = t.card := by
  simp [binomialMoment]

/-- The first binomial moment is the exact total occupancy. -/
@[simp]
theorem binomialMoment_one (t : Finset β) (n : β → ℕ) :
    binomialMoment t n 1 = ∑ b ∈ t, n b := by
  simp [binomialMoment]

@[simp]
theorem truncatedBinomial_zero (k : ℕ) : truncatedBinomial 0 k = 0 := by
  simp [truncatedBinomial]

@[simp]
theorem truncatedBinomial_order_zero (n : ℕ) : truncatedBinomial n 0 = 0 := by
  simp [truncatedBinomial]

/-- Exact pointwise truncated alternating-binomial identity for positive occupancy. -/
theorem truncatedBinomial_succ (n k : ℕ) :
    truncatedBinomial (n + 1) k =
      1 - (-1 : ℝ) ^ k * (n.choose k : ℝ) := by
  induction k with
  | zero => simp [truncatedBinomial]
  | succ k hk =>
    calc
      truncatedBinomial (n + 1) (k + 1) =
          truncatedBinomial (n + 1) k +
            (-1 : ℝ) ^ k * ((n + 1).choose (k + 1) : ℝ) := by
        simp [truncatedBinomial, Finset.sum_range_succ]
      _ = 1 - (-1 : ℝ) ^ (k + 1) * (n.choose (k + 1) : ℝ) := by
        rw [hk, Nat.choose_succ_succ, Nat.cast_add, pow_succ]
        ring

theorem truncatedBinomial_of_pos {n : ℕ} (hn : 0 < n) (k : ℕ) :
    truncatedBinomial n k =
      1 - (-1 : ℝ) ^ k * ((n - 1).choose k : ℝ) := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  simpa using truncatedBinomial_succ a k

/-- The exact identity with the empty-occupancy case included. -/
theorem truncatedBinomial_eq (n k : ℕ) :
    truncatedBinomial n k =
      if 0 < n then 1 - (-1 : ℝ) ^ k * ((n - 1).choose k : ℝ) else 0 := by
  by_cases hn : 0 < n
  · simp [hn, truncatedBinomial_of_pos hn]
  · have hz : n = 0 := by omega
    simp [hz]

/-- Even truncations lie below the indicator of positive occupancy. -/
theorem truncatedBinomial_even_le (n m : ℕ) :
    truncatedBinomial n (2 * m) ≤ (if 0 < n then (1 : ℝ) else 0) := by
  cases n with
  | zero => simp
  | succ n =>
    simp only [truncatedBinomial_succ, pow_mul, neg_one_sq, one_pow, one_mul,
      Nat.zero_lt_succ, ite_true]
    exact sub_le_self _ (Nat.cast_nonneg _)

/-- Odd truncations lie above the indicator of positive occupancy. -/
theorem le_truncatedBinomial_odd (n m : ℕ) :
    (if 0 < n then (1 : ℝ) else 0) ≤ truncatedBinomial n (2 * m + 1) := by
  cases n with
  | zero => simp
  | succ n =>
    simp only [truncatedBinomial_succ, pow_add, pow_mul, neg_one_sq, one_pow,
      pow_one, one_mul, neg_mul, sub_neg_eq_add, Nat.zero_lt_succ, ite_true]
    exact le_add_of_nonneg_right (Nat.cast_nonneg _)

/-- Once the truncation order is at least the occupancy, the answer is exact. -/
theorem truncatedBinomial_eq_indicator_of_le (n k : ℕ) (h : n ≤ k) :
    truncatedBinomial n k = (if 0 < n then (1 : ℝ) else 0) := by
  cases n with
  | zero => simp
  | succ n =>
    have hnk : n < k := by omega
    simp [truncatedBinomial_succ, Nat.choose_eq_zero_of_lt hnk]

/-- Real indicator-sum formula for the occupied cardinality. -/
theorem occupied_cast_eq_sum (t : Finset β) (n : β → ℕ) :
    (occupied t n : ℝ) = ∑ b ∈ t, if 0 < n b then (1 : ℝ) else 0 := by
  simp [occupied]

/-- Interchanging the two finite sums reduces occupancy bounds to pointwise bounds. -/
theorem bonferroniSum_eq_sum_truncated (t : Finset β) (n : β → ℕ) (k : ℕ) :
    bonferroniSum t n k = ∑ b ∈ t, truncatedBinomial (n b) k := by
  simp only [bonferroniSum, binomialMoment, Nat.cast_sum, Finset.mul_sum,
    truncatedBinomial]
  rw [Finset.sum_comm]

/-- Unshifted form, with the sign and endpoints in the usual Bonferroni convention. -/
theorem bonferroniSum_eq_Icc (t : Finset β) (n : β → ℕ) (k : ℕ) :
    bonferroniSum t n k =
      ∑ r ∈ Finset.Icc 1 k, (-1 : ℝ) ^ (r + 1) * (binomialMoment t n r : ℝ) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel, bonferroniSum]
  apply Finset.sum_congr rfl
  intro r _
  simp [pow_add, Nat.add_comm]

@[simp]
theorem bonferroniSum_zero (t : Finset β) (n : β → ℕ) :
    bonferroniSum t n 0 = 0 := by
  simp [bonferroniSum]

@[simp]
theorem bonferroniSum_one (t : Finset β) (n : β → ℕ) :
    bonferroniSum t n 1 = (∑ b ∈ t, n b : ℕ) := by
  simp [bonferroniSum]

/-- Exact remainder formula; the remaining binomial sum is nonnegative. -/
theorem bonferroniSum_eq_occupied_sub (t : Finset β) (n : β → ℕ) (k : ℕ) :
    bonferroniSum t n k = (occupied t n : ℝ) - (-1 : ℝ) ^ k *
      ((∑ b ∈ t.filter (fun b => 0 < n b), (n b - 1).choose k : ℕ) : ℝ) := by
  rw [bonferroniSum_eq_sum_truncated, occupied_cast_eq_sum, Nat.cast_sum,
    Finset.sum_filter, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hn : 0 < n b
  · simp [hn, truncatedBinomial_of_pos hn]
  · have hz : n b = 0 := by omega
    simp [hz]

/-- Lower Bonferroni bound for an arbitrary finite occupancy map. -/
theorem bonferroni_even_le_occupied (t : Finset β) (n : β → ℕ) (m : ℕ) :
    bonferroniSum t n (2 * m) ≤ (occupied t n : ℝ) := by
  rw [bonferroniSum_eq_sum_truncated, occupied_cast_eq_sum]
  exact Finset.sum_le_sum fun b _ => truncatedBinomial_even_le (n b) m

/-- Upper Bonferroni bound for an arbitrary finite occupancy map. -/
theorem occupied_le_bonferroni_odd (t : Finset β) (n : β → ℕ) (m : ℕ) :
    (occupied t n : ℝ) ≤ bonferroniSum t n (2 * m + 1) := by
  rw [bonferroniSum_eq_sum_truncated, occupied_cast_eq_sum]
  exact Finset.sum_le_sum fun b _ => le_truncatedBinomial_odd (n b) m

/-- Both Bonferroni bounds, expressed as sums over orders starting at one. -/
theorem bonferroni_bounds (t : Finset β) (n : β → ℕ) (m : ℕ) :
    (∑ r ∈ Finset.Icc 1 (2 * m),
      (-1 : ℝ) ^ (r + 1) * (binomialMoment t n r : ℝ)) ≤ (occupied t n : ℝ) ∧
    (occupied t n : ℝ) ≤ ∑ r ∈ Finset.Icc 1 (2 * m + 1),
      (-1 : ℝ) ^ (r + 1) * (binomialMoment t n r : ℝ) := by
  simpa only [← bonferroniSum_eq_Icc] using
    And.intro (bonferroni_even_le_occupied t n m) (occupied_le_bonferroni_odd t n m)

/-- Full finite inclusion-exclusion: any order bounding all occupancies is exact. -/
theorem bonferroniSum_eq_occupied_of_le (t : Finset β) (n : β → ℕ) (k : ℕ)
    (h : ∀ b ∈ t, n b ≤ k) :
    bonferroniSum t n k = (occupied t n : ℝ) := by
  rw [bonferroniSum_eq_sum_truncated, occupied_cast_eq_sum]
  exact Finset.sum_congr rfl fun b hb => truncatedBinomial_eq_indicator_of_le (n b) k (h b hb)

section Fibers

variable {α : Type*} [DecidableEq β]

/-- Cardinality of the fiber over `b`, restricted to the finite source `s`. -/
def fiberCard (s : Finset α) (f : α → β) (b : β) : ℕ :=
  (s.filter fun a => f a = b).card

@[simp]
theorem fiberCard_pos_iff (s : Finset α) (f : α → β) (b : β) :
    0 < fiberCard s f b ↔ b ∈ s.image f := by
  simp [fiberCard, Finset.card_pos, Finset.filter_nonempty_iff, Finset.mem_image]

theorem fiberCard_le_card (s : Finset α) (f : α → β) (b : β) :
    fiberCard s f b ≤ s.card :=
  Finset.card_le_card (Finset.filter_subset _ _)

/-- Exact fiber total over any target set, even one not containing the whole image. -/
theorem sum_fiberCard_eq_card_filter (s : Finset α) (f : α → β) (t : Finset β) :
    ∑ b ∈ t, fiberCard s f b = (s.filter fun a => f a ∈ t).card := by
  exact Finset.sum_card_fiberwise_eq_card_filter s t f

/-- Summing all restricted fibers gives the exact source cardinality. -/
theorem sum_fiberCard_eq_card_of_subset (s : Finset α) (f : α → β) (t : Finset β)
    (h : s.image f ⊆ t) :
    ∑ b ∈ t, fiberCard s f b = s.card := by
  exact (Finset.card_eq_sum_card_fiberwise fun a ha =>
    h (Finset.mem_image_of_mem f ha)).symm

@[simp]
theorem sum_fiberCard_image (s : Finset α) (f : α → β) :
    ∑ b ∈ s.image f, fiberCard s f b = s.card := by
  exact sum_fiberCard_eq_card_of_subset s f (s.image f) Finset.Subset.rfl

/-- In particular, `S_1` for finite fibers is exactly the source cardinality. -/
theorem binomialMoment_fiber_one_of_subset (s : Finset α) (f : α → β) (t : Finset β)
    (h : s.image f ⊆ t) :
    binomialMoment t (fiberCard s f) 1 = s.card := by
  rw [binomialMoment_one, sum_fiberCard_eq_card_of_subset s f t h]

@[simp]
theorem binomialMoment_fiber_image_one (s : Finset α) (f : α → β) :
    binomialMoment (s.image f) (fiberCard s f) 1 = s.card := by
  simp

/-- Occupied targets are precisely the targets that occur in the image. -/
theorem occupied_fiberCard_eq_card_inter (s : Finset α) (f : α → β) (t : Finset β) :
    occupied t (fiberCard s f) = (t ∩ s.image f).card := by
  simp only [occupied, fiberCard_pos_iff, Finset.filter_mem_eq_inter]

theorem occupied_fiberCard_eq_card_image_of_subset
    (s : Finset α) (f : α → β) (t : Finset β) (h : s.image f ⊆ t) :
    occupied t (fiberCard s f) = (s.image f).card := by
  rw [occupied_fiberCard_eq_card_inter, Finset.inter_eq_right.mpr h]

@[simp]
theorem occupied_fiberCard_image (s : Finset α) (f : α → β) :
    occupied (s.image f) (fiberCard s f) = (s.image f).card := by
  exact occupied_fiberCard_eq_card_image_of_subset s f (s.image f) Finset.Subset.rfl

/-- Image-cardinality Bonferroni bounds, summing fibers over any finite set
containing the image. The ambient target type need not be finite. -/
theorem card_image_bonferroni_of_subset
    (s : Finset α) (f : α → β) (t : Finset β) (h : s.image f ⊆ t) (m : ℕ) :
    (∑ r ∈ Finset.Icc 1 (2 * m),
      (-1 : ℝ) ^ (r + 1) * (binomialMoment t (fiberCard s f) r : ℝ)) ≤
        ((s.image f).card : ℝ) ∧
    ((s.image f).card : ℝ) ≤ ∑ r ∈ Finset.Icc 1 (2 * m + 1),
      (-1 : ℝ) ^ (r + 1) * (binomialMoment t (fiberCard s f) r : ℝ) := by
  simpa only [occupied_fiberCard_eq_card_image_of_subset s f t h] using
    bonferroni_bounds t (fiberCard s f) m

/-- Image-cardinality Bonferroni bounds with the canonical target set `s.image f`. -/
theorem card_image_bonferroni (s : Finset α) (f : α → β) (m : ℕ) :
    (∑ r ∈ Finset.Icc 1 (2 * m), (-1 : ℝ) ^ (r + 1) *
      (binomialMoment (s.image f) (fiberCard s f) r : ℝ)) ≤ ((s.image f).card : ℝ) ∧
    ((s.image f).card : ℝ) ≤ ∑ r ∈ Finset.Icc 1 (2 * m + 1), (-1 : ℝ) ^ (r + 1) *
      (binomialMoment (s.image f) (fiberCard s f) r : ℝ) := by
  exact card_image_bonferroni_of_subset s f (s.image f) Finset.Subset.rfl m

/-- Exact inclusion-exclusion for image cardinality at any order bounding the fibers. -/
theorem bonferroniSum_fiber_eq_card_image_of_le
    (s : Finset α) (f : α → β) (t : Finset β) (h : s.image f ⊆ t) (k : ℕ)
    (hk : ∀ b ∈ t, fiberCard s f b ≤ k) :
    bonferroniSum t (fiberCard s f) k = ((s.image f).card : ℝ) := by
  rw [bonferroniSum_eq_occupied_of_le t (fiberCard s f) k hk,
    occupied_fiberCard_eq_card_image_of_subset s f t h]

/-- The source cardinality is always a sufficient order for exact inclusion-exclusion. -/
theorem card_image_eq_alternating_sum (s : Finset α) (f : α → β) :
    ((s.image f).card : ℝ) = ∑ r ∈ Finset.Icc 1 s.card, (-1 : ℝ) ^ (r + 1) *
      (binomialMoment (s.image f) (fiberCard s f) r : ℝ) := by
  rw [← bonferroniSum_eq_Icc]
  exact (bonferroniSum_fiber_eq_card_image_of_le s f (s.image f) Finset.Subset.rfl
    s.card fun b _ => fiberCard_le_card s f b).symm

end Fibers

end OccupancyBounds
