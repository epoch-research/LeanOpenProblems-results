import FormalConjecturesUtil

/-! Finite partial summation for the logarithmically weighted Type-I terms. -/
namespace Erdos972ExponentialSum
open Finset

lemma norm_monotone_weighted_prefix {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (w : ℕ → ℝ) (hw : Monotone w) (hw0 : 0 ≤ w 0)
    (z : ℕ → E) (K : ℕ) (B : ℝ)
    (hB : ∀ j ≤ K, ‖∑ n ∈ range j, z n‖ ≤ B) :
    ‖∑ n ∈ range K, w n • z n‖ ≤ 2 * w (K - 1) * B := by
  have hB0 : 0 ≤ B := by simpa using hB 0 (Nat.zero_le K)
  have hwK : 0 ≤ w (K - 1) := hw0.trans (hw (Nat.zero_le _))
  rw [sum_range_by_parts]
  calc
    _ ≤ ‖w (K - 1) • ∑ n ∈ range K, z n‖ +
        ‖∑ i ∈ range (K - 1), (w (i + 1) - w i) • ∑ n ∈ range (i + 1), z n‖ :=
      norm_sub_le _ _
    _ ≤ w (K - 1) * B + ∑ i ∈ range (K - 1), (w (i + 1) - w i) * B := by
      apply add_le_add
      · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hwK]
        exact mul_le_mul_of_nonneg_left (hB K le_rfl) hwK
      · apply (norm_sum_le _ _).trans
        apply sum_le_sum
        intro i hi
        have hd : 0 ≤ w (i + 1) - w i := sub_nonneg.mpr (hw (Nat.le_succ _))
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hd]
        exact mul_le_mul_of_nonneg_left (hB (i + 1) (by have := mem_range.mp hi; omega)) hd
    _ = (2 * w (K - 1) - w 0) * B := by
      rw [← sum_mul, sum_range_sub]
      ring
    _ ≤ _ := by nlinarith

lemma monotone_log_natCast : Monotone (fun n : ℕ => Real.log n) := by
  intro m n hmn
  by_cases hm : m = 0
  · simpa [hm] using Real.log_natCast_nonneg n
  · exact Real.log_le_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm))
      (Nat.cast_le.mpr hmn)

lemma norm_log_weighted_prefix {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (z : ℕ → E) (K : ℕ) (B : ℝ)
    (hB : ∀ j ≤ K, ‖∑ n ∈ range j, z n‖ ≤ B) :
    ‖∑ n ∈ range K, Real.log n • z n‖ ≤ 2 * Real.log K * B := by
  have hB0 : 0 ≤ B := by simpa using hB 0 (Nat.zero_le K)
  apply (norm_monotone_weighted_prefix (fun n => Real.log n)
    monotone_log_natCast (by simp) z K B hB).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (monotone_log_natCast (Nat.sub_le K 1)) (by norm_num)) hB0

/-- Truncating a prefix by a second prefix takes the minimum of the lengths. -/
lemma sum_range_ite_lt {E : Type*} [AddCommMonoid E]
    (f : ℕ → E) (j k : ℕ) :
    (∑ n ∈ range j, if n < k then f n else 0) = ∑ n ∈ range (min j k), f n := by
  classical
  rw [← sum_filter]
  congr 1
  ext n
  simp only [mem_filter, mem_range, lt_min_iff]

/-- A uniform bound for all row-prefix cutoffs also controls a common monotone
weight in the inner variable, at the standard partial-summation cost. -/
lemma norm_monotone_weighted_rows {ι E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (s : Finset ι) (A : ι → ℕ → E) (K : ι → ℕ)
    (L : ℕ) (hK : ∀ m ∈ s, K m ≤ L)
    (w : ℕ → ℝ) (hw : Monotone w) (hw0 : 0 ≤ w 0) (B : ℝ)
    (hB : ∀ F : ι → ℕ, (∀ m ∈ s, F m ≤ K m) →
      ‖∑ m ∈ s, ∑ n ∈ range (F m), A m n‖ ≤ B) :
    ‖∑ m ∈ s, ∑ n ∈ range (K m), w n • A m n‖ ≤ 2 * w L * B := by
  classical
  let z : ℕ → E := fun n => ∑ m ∈ s, if n < K m then A m n else 0
  have hz (j : ℕ) :
      (∑ n ∈ range j, z n) = ∑ m ∈ s, ∑ n ∈ range (min j (K m)), A m n := by
    dsimp only [z]
    rw [sum_comm]
    apply sum_congr rfl
    intro m hm
    exact sum_range_ite_lt _ _ _
  have hzb (j : ℕ) : ‖∑ n ∈ range j, z n‖ ≤ B := by
    rw [hz]
    exact hB (fun m => min j (K m)) (fun m hm => min_le_right _ _)
  have hB0 : 0 ≤ B := by simpa using hzb 0
  have he : (∑ n ∈ range L, w n • z n) =
      ∑ m ∈ s, ∑ n ∈ range (K m), w n • A m n := by
    dsimp only [z]
    simp_rw [smul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro m hm
    simp_rw [smul_ite, smul_zero]
    rw [sum_range_ite_lt, min_eq_right (hK m hm)]
  rw [← he]
  apply (norm_monotone_weighted_prefix w hw hw0 z L B
    (fun j hj => hzb j)).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hw (Nat.sub_le L 1)) (by norm_num)) hB0

#print axioms norm_monotone_weighted_rows
#print axioms norm_monotone_weighted_prefix
#print axioms norm_log_weighted_prefix
end Erdos972ExponentialSum
