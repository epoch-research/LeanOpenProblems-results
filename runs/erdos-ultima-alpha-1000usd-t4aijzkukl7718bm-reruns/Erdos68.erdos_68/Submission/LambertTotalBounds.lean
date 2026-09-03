import Submission.LambertTailRows

/-! Uniform total error bounds for finite raw Lambert operators, with all
infinite-sum interchanges verified. Nonvanishing of integer forms is not
established here. -/
namespace LambertTotalBounds

open Finset Erdos68Development LambertDifferenceOperators LambertRawBounds LambertTailRows

lemma cutoff_tail_rows (ds : List ℕ) (K n : ℕ)
    (hcancel : ∀ k < K, k + 2 ∈ ds) :
    rawApply ds (fun n => (∑' k : ℕ, term k) - (prefixQ n : ℝ)) n =
      ∑' k : ℕ, rawApply ds (geometricRowTail (k + K + 2)) n := by
  rw [rawApply_tail_rows]
  have hs : Summable (fun k => rawApply ds (geometricRowTail (k + 2)) n) := by
    simpa only [row] using summable_rawApply ds row summable_row n
  have hz : (∑ k ∈ Finset.range K, rawApply ds (geometricRowTail (k + 2)) n) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    exact congrFun (rawApply_geometricRowTail_zero ds (k + 2) (by omega)
      (hcancel k (Finset.mem_range.mp hk))) n
  have h := hs.sum_add_tsum_nat_add K
  rw [hz, zero_add] at h
  exact h.symm

lemma summable_bound (C : ℝ) (K m : ℕ) (hm : 1 < m) :
    Summable (fun k : ℕ => C / ((k + K + 2 : ℕ) : ℝ) ^ m) := by
  have hs : Summable (fun k : ℕ => 1 / (k : ℝ) ^ m) :=
    Real.summable_one_div_nat_pow.mpr hm
  have ht := (summable_nat_add_iff (K + 2)).mpr hs
  simpa [Nat.add_assoc, mul_div_assoc] using ht.mul_left C

theorem total_pseries_bound (ds : List ℕ) (K n : ℕ) (hn : 1 < n / 2)
    (hcancel : ∀ k < K, k + 2 ∈ ds)
    (hsize : ∀ k ∈ ds, k ≤ K + 2) :
    |rawApply ds (fun n => (∑' k : ℕ, term k) - (prefixQ n : ℝ)) n| ≤
      ∑' k : ℕ, 2 ^ (ds.length + 1) / ((k + K + 2 : ℕ) : ℝ) ^ (n / 2) := by
  rw [cutoff_tail_rows ds K n hcancel]
  have hs := summable_bound (2 ^ (ds.length + 1)) K (n / 2) hn
  have h := tsum_of_norm_bounded
    (f := fun k => rawApply ds (geometricRowTail (k + K + 2)) n) hs.hasSum (fun k => by
    simpa only [Real.norm_eq_abs] using rawApply_row_bound_floor ds (k + K + 2) n
      (by omega) (fun j hj => (hsize j hj).trans (by omega)))
  simpa only [Real.norm_eq_abs] using h

/-- The first K rows, d=2,...,K+1, are removed. -/
theorem range_operator_bound (K n : ℕ) (hn : 1 < n / 2) :
    |rawApply (List.range' 2 K)
      (fun n => (∑' k : ℕ, term k) - (prefixQ n : ℝ)) n| ≤
      ∑' k : ℕ, 2 ^ (K + 1) / ((k + K + 2 : ℕ) : ℝ) ^ (n / 2) := by
  have hc : ∀ k < K, k + 2 ∈ List.range' 2 K := by
    intro k hk
    exact List.mem_range'.mpr ⟨k, hk, by omega⟩
  have hs : ∀ k ∈ List.range' 2 K, k ≤ K + 2 := by
    intro k hk
    obtain ⟨i, hi, he⟩ := List.mem_range'.mp hk
    omega
  simpa only [List.length_range'] using total_pseries_bound (List.range' 2 K) K n hn hc hs


open Filter
open scoped Topology

lemma hasSum_reciprocal_differences (K : ℕ) :
    HasSum (fun k : ℕ => 1 / ((k + K + 1 : ℕ) : ℝ) -
      1 / ((k + K + 2 : ℕ) : ℝ)) (1 / ((K + 1 : ℕ) : ℝ)) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun k => by
    apply sub_nonneg.mpr
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast (show k + K + 1 ≤ k + K + 2 by omega))) _).mpr
  have he (N : ℕ) : (∑ k ∈ Finset.range N,
      (1 / ((k + K + 1 : ℕ) : ℝ) - 1 / ((k + K + 2 : ℕ) : ℝ))) =
      1 / ((K + 1 : ℕ) : ℝ) - 1 / ((N + K + 1 : ℕ) : ℝ) := by
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      Finset.sum_range_sub' (fun k => 1 / ((k + K + 1 : ℕ) : ℝ)) N
  simp_rw [he]
  have ht : Tendsto (fun n : ℕ => 1 / ((n + K + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    simpa [Nat.add_assoc] using
      (tendsto_add_atTop_iff_nat (K + 1)).mpr
        (tendsto_one_div_atTop_nhds_zero_nat : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0))
  simpa using (tendsto_const_nhds.sub ht)

lemma pseries_term_le (K m k : ℕ) (hm : 2 ≤ m) :
    1 / ((k + K + 2 : ℕ) : ℝ) ^ m ≤
      (1 / ((K + 1 : ℕ) : ℝ) ^ (m - 2)) *
        (1 / ((k + K + 1 : ℕ) : ℝ) - 1 / ((k + K + 2 : ℕ) : ℝ)) := by
  have hb : (0 : ℝ) < (K + 1 : ℕ) := by positivity
  have hx : (0 : ℝ) < (k + K + 1 : ℕ) := by positivity
  have hy : (0 : ℝ) < (k + K + 2 : ℕ) := by positivity
  have hbxy : ((K + 1 : ℕ) : ℝ) ≤ (k + K + 2 : ℕ) := by exact_mod_cast (show K + 1 ≤ k + K + 2 by omega)
  have hxy : ((k + K + 1 : ℕ) : ℝ) ≤ (k + K + 2 : ℕ) := by exact_mod_cast (show k + K + 1 ≤ k + K + 2 by omega)
  have hp : ((K + 1 : ℕ) : ℝ) ^ (m - 2) *
      (((k + K + 1 : ℕ) : ℝ) * ((k + K + 2 : ℕ) : ℝ)) ≤
      ((k + K + 2 : ℕ) : ℝ) ^ m := by
    calc
      _ ≤ ((k + K + 2 : ℕ) : ℝ) ^ (m - 2) *
          (((k + K + 2 : ℕ) : ℝ) * ((k + K + 2 : ℕ) : ℝ)) := by gcongr
      _ = _ := by rw [← pow_two, ← pow_add, Nat.sub_add_cancel hm]
  calc
    _ ≤ 1 / (((K + 1 : ℕ) : ℝ) ^ (m - 2) *
        (((k + K + 1 : ℕ) : ℝ) * ((k + K + 2 : ℕ) : ℝ))) :=
      one_div_le_one_div_of_le (by positivity) hp
    _ = _ := by
      have he : ((k + K + 2 : ℕ) : ℝ) = ((k + K + 1 : ℕ) : ℝ) + 1 := by push_cast; ring
      rw [he]
      field_simp
      ring

lemma pseries_tail_bound (K m : ℕ) (hm : 2 ≤ m) :
    (∑' k : ℕ, 1 / ((k + K + 2 : ℕ) : ℝ) ^ m) ≤
      1 / ((K + 1 : ℕ) : ℝ) ^ (m - 1) := by
  have hs := summable_bound 1 K m (by omega)
  have ht := (hasSum_reciprocal_differences K).mul_left
    (1 / ((K + 1 : ℕ) : ℝ) ^ (m - 2))
  have h := Summable.tsum_le_tsum (pseries_term_le K m · hm) hs ht.summable
  rw [ht.tsum_eq] at h
  have he : (1 / ((K + 1 : ℕ) : ℝ) ^ (m - 2)) *
      (1 / ((K + 1 : ℕ) : ℝ)) = 1 / ((K + 1 : ℕ) : ℝ) ^ (m - 1) := by
    rw [show m - 1 = (m - 2) + 1 by omega, pow_succ, one_div_mul_one_div]
  exact he ▸ h

/-- A completely explicit uniform bound for the raw error. -/
theorem range_operator_explicit_bound (K n : ℕ) (hn : 4 ≤ n) :
    |rawApply (List.range' 2 K)
      (fun n => (∑' k : ℕ, term k) - (prefixQ n : ℝ)) n| ≤
      2 ^ (K + 1) / ((K + 1 : ℕ) : ℝ) ^ (n / 2 - 1) := by
  have hm : 2 ≤ n / 2 := by omega
  calc
    _ ≤ ∑' k : ℕ, 2 ^ (K + 1) / ((k + K + 2 : ℕ) : ℝ) ^ (n / 2) :=
      range_operator_bound K n (by omega)
    _ = 2 ^ (K + 1) * (∑' k : ℕ, 1 / ((k + K + 2 : ℕ) : ℝ) ^ (n / 2)) := by
      simp only [div_eq_mul_inv, one_mul, tsum_mul_left]
    _ ≤ 2 ^ (K + 1) * (1 / ((K + 1 : ℕ) : ℝ) ^ (n / 2 - 1)) :=
      mul_le_mul_of_nonneg_left (pseries_tail_bound K (n / 2) hm) (by positivity)
    _ = _ := by ring

end LambertTotalBounds

#print axioms LambertTotalBounds.cutoff_tail_rows
#print axioms LambertTotalBounds.total_pseries_bound
#print axioms LambertTotalBounds.range_operator_bound

#print axioms LambertTotalBounds.pseries_tail_bound
#print axioms LambertTotalBounds.range_operator_explicit_bound
