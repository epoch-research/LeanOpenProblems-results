import FormalConjecturesUtil
import Submission.SeparateAlladi
import Submission.DivisorReindex
import Submission.CofactorDiscrepancy

/-! The signed count as a Möbius-weighted discrepancy in arithmetic progressions.
No cancellation estimate for this expression is assumed or proved here. -/

namespace Erdos371RawDiscrepancy

open Erdos371SeparateAlladi Erdos371DivisorReindex Erdos371PrimeDiscrepancy
open Erdos371CofactorDiscrepancy

def left (m : ℕ) : ℤ := ∑ d ∈ m.divisors, roughWeight (P (m + 1)) d

def right (m : ℕ) : ℤ := ∑ d ∈ m.divisors, roughWeight (P (m - 1)) d

lemma sign_eq_left_sub_right (n : ℕ) :
    sign n = (if n = 0 then 1 else 0) + left n - right (n + 1) := by
  rcases n with _ | _ | n
  · decide +kernel
  · decide +kernel
  · simpa [left, right] using separate_divisor_expansion (n := n + 2) (by omega)

lemma left_eq_neg_endpoint (N : ℕ) :
    left N = -(if P (N + 1) < P N then 1 else 0) := by
  rcases N with _ | _ | N
  · decide +kernel
  · decide +kernel
  · exact alladi_divisor_form (by omega : 1 < N + 2) _

lemma divisor_total_range {N : ℕ} (hN : 0 < N) :
    (∑ m ∈ Finset.range (N + 1), (left m - right m)) =
      total N - 1 - (if P (N + 1) < P N then 1 else 0) := by
  have ht : total N = 1 + ∑ n ∈ Finset.range N, (left n - right (n + 1)) := by
    unfold total
    simp_rw [sign_eq_left_sub_right]
    have he (n : ℕ) :
        (if n = 0 then (1 : ℤ) else 0) + left n - right (n + 1) =
          (if n = 0 then 1 else 0) + (left n - right (n + 1)) := by ring
    simp_rw [he]
    rw [Finset.sum_add_distrib]
    have hm : 0 ∈ Finset.range N := Finset.mem_range.mpr hN
    simp [hm]
  rw [Finset.sum_sub_distrib, Finset.sum_range_succ]
  have hr : (∑ m ∈ Finset.range (N + 1), right m) =
      ∑ n ∈ Finset.range N, right (n + 1) := by
    rw [Finset.sum_range_succ']
    have hzero : right 0 = 0 := by decide +kernel
    simp [hzero]
  rw [hr, left_eq_neg_endpoint]
  rw [Finset.sum_sub_distrib] at ht
  omega

lemma sum_Icc_eq_sum_range_of_zero (N : ℕ) (f : ℕ → ℤ) (hzero : f 0 = 0) :
    (∑ m ∈ Finset.Icc 1 N, f m) = ∑ m ∈ Finset.range (N + 1), f m := by
  have he : insert 0 (Finset.Icc 1 N) = Finset.range (N + 1) := by
    ext m
    simp only [Finset.mem_insert, Finset.mem_Icc, Finset.mem_range]
    omega
  rw [← he, Finset.sum_insert (by simp), hzero, zero_add]

def raw (d N : ℕ) : ℤ :=
  ∑ k ∈ Finset.Icc 1 (N / d),
    (roughWeight (P (k * d + 1)) d - roughWeight (P (k * d - 1)) d)

lemma raw_sum_eq_total {N : ℕ} (hN : 0 < N) :
    (∑ d ∈ Finset.Icc 1 N, raw d N) =
      total N - 1 - (if P (N + 1) < P N then 1 else 0) := by
  have he : (∑ d ∈ Finset.Icc 1 N, raw d N) =
      ∑ m ∈ Finset.Icc 1 N, (left m - right m) := by
    unfold raw
    rw [← sum_divisors_reindex N (fun d m => roughWeight (P (m + 1)) d - roughWeight (P (m - 1)) d)]
    apply Finset.sum_congr rfl
    intro m hm
    simp only [left, right, Finset.sum_sub_distrib]
  rw [he, sum_Icc_eq_sum_range_of_zero N (fun m => left m - right m)
    (by decide +kernel)]
  exact divisor_total_range hN

lemma raw_sum_eq_cofactor_sum {N : ℕ} (hN : 0 < N) :
    (∑ d ∈ Finset.Icc 1 N, raw d N) =
      ∑ p ∈ (N + 1).primesBelow, cofactorDifference p N := by
  rw [raw_sum_eq_total hN]
  have he := total_eq_cofactor_sum hN
  omega

lemma raw_eq_moebius_mul_counts {d : ℕ} (hd : 1 < d) (N : ℕ) :
    raw d N = ArithmeticFunction.moebius d *
      ((((Finset.Icc 1 (N / d)).filter (fun k => P (k * d + 1) < d.minFac)).card : ℤ) -
        (((Finset.Icc 1 (N / d)).filter (fun k => P (k * d - 1) < d.minFac)).card : ℤ)) := by
  have he (k : ℕ) :
      roughWeight (P (k * d + 1)) d - roughWeight (P (k * d - 1)) d =
        ArithmeticFunction.moebius d *
          ((if P (k * d + 1) < d.minFac then (1 : ℤ) else 0) -
            (if P (k * d - 1) < d.minFac then 1 else 0)) := by
    unfold roughWeight
    simp only [hd, true_and]
    split_ifs <;> ring
  simp only [raw, he, ← Finset.mul_sum, Finset.sum_sub_distrib]
  simp

open Filter
open scoped Topology

lemma density_half_iff_raw_discrepancy :
    {n | P n < P (n + 1)}.HasDensity (1 / 2) ↔
      Tendsto (fun N : ℕ => ((∑ d ∈ Finset.Icc 1 N, raw d N : ℤ) : ℝ) / N)
        atTop (𝓝 0) := by
  rw [density_half_iff_cofactor_discrepancy]
  constructor
  · intro h
    apply h.congr'
    filter_upwards [eventually_gt_atTop 0] with N hN
    rw [raw_sum_eq_cofactor_sum hN]
  · intro h
    apply h.congr'
    filter_upwards [eventually_gt_atTop 0] with N hN
    rw [raw_sum_eq_cofactor_sum hN]

end Erdos371RawDiscrepancy

#print axioms Erdos371RawDiscrepancy.divisor_total_range

#print axioms Erdos371RawDiscrepancy.raw_sum_eq_total
#print axioms Erdos371RawDiscrepancy.raw_eq_moebius_mul_counts
#print axioms Erdos371RawDiscrepancy.density_half_iff_raw_discrepancy
