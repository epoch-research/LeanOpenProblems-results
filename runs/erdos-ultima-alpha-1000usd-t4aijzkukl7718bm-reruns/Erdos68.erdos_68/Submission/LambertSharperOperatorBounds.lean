import Submission.LambertTotalBounds

/-! Sharper analytic estimates for the raw operators. These do not prove
nonvanishing or settle the irrationality conjecture. -/

namespace LambertSharperOperatorBounds

open Finset Erdos68Development LambertDifferenceOperators LambertRawBounds
  LambertTailRows LambertTotalBounds

lemma rate_lower_exp (d : ℕ) (hd : 0 < d) :
    (d : ℝ) / Real.exp 1 ≤ rate d := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hs : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi * d) := by
    apply Real.one_le_sqrt.mpr
    nlinarith [Real.pi_gt_three]
  have hp : ((d : ℝ) / Real.exp 1) ^ d ≤ (d.factorial : ℝ) := by
    calc
      _ ≤ Real.sqrt (2 * Real.pi * d) * ((d : ℝ) / Real.exp 1) ^ d := by
        nlinarith [pow_nonneg (show 0 ≤ (d : ℝ) / Real.exp 1 by positivity) d]
      _ ≤ _ := Stirling.le_factorial_stirling d
  apply le_of_pow_le_pow_left₀ hd.ne' (rate_pos d).le
  simpa only [rate_pow d hd] using hp

lemma rate_lower_third (d : ℕ) (hd : 0 < d) : (d : ℝ) / 3 ≤ rate d := by
  calc
    (d : ℝ) / 3 ≤ (d : ℝ) / Real.exp 1 := by
      apply div_le_div_of_nonneg_left (Nat.cast_nonneg d) (Real.exp_pos 1)
      exact Real.exp_one_lt_d9.le.trans (by norm_num)
    _ ≤ _ := rate_lower_exp d hd

noncomputable def weightedFactor (d : ℕ) (x : ℝ) : ℝ :=
  1 + (d.factorial : ℝ) / x ^ d

noncomputable def weightedProduct (ds : List ℕ) (x : ℝ) : ℝ :=
  (ds.map (fun d => weightedFactor d x)).prod

lemma weightedFactor_nonneg (d : ℕ) (x : ℝ) (hx : 0 < x) :
    0 ≤ weightedFactor d x := by unfold weightedFactor; positivity

lemma weightedProduct_nonneg (ds : List ℕ) (x : ℝ) (hx : 0 < x) :
    0 ≤ weightedProduct ds x := by
  unfold weightedProduct
  apply List.prod_nonneg
  intro a ha
  obtain ⟨d, _, rfl⟩ := List.mem_map.mp ha
  exact weightedFactor_nonneg d x hx

lemma rawShift_weighted_bound (d : ℕ) (r : ℕ → ℝ) (x C : ℝ)
    (hx : 0 < x) (hr : ∀ n, |r n| ≤ C / x ^ n) (n : ℕ) :
    |rawShift d r n| ≤ weightedFactor d x * C / x ^ n := by
  unfold rawShift
  calc
    _ ≤ |(d.factorial : ℝ) * r (n + d)| + |r n| := abs_sub _ _
    _ = (d.factorial : ℝ) * |r (n + d)| + |r n| := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    _ ≤ (d.factorial : ℝ) * (C / x ^ (n + d)) + C / x ^ n := by
      gcongr
      · exact hr (n + d)
      · exact hr n
    _ = _ := by
      unfold weightedFactor
      rw [pow_add]
      field_simp
      ring

lemma rawApply_weighted_bound (ds : List ℕ) (r : ℕ → ℝ) (x C : ℝ)
    (hx : 0 < x) (hC : 0 ≤ C) (hr : ∀ n, |r n| ≤ C / x ^ n) (n : ℕ) :
    |rawApply ds r n| ≤ weightedProduct ds x * C / x ^ n := by
  induction ds generalizing r C with
  | nil => simpa [rawApply, weightedProduct] using hr n
  | cons d ds ih =>
    have hb := rawShift_weighted_bound d r x C hx hr
    have hi := ih (rawShift d r) (weightedFactor d x * C)
      (mul_nonneg (weightedFactor_nonneg d x hx) hC) hb
    simpa [rawApply, weightedProduct, mul_assoc, mul_left_comm, mul_comm] using hi

/-- The exact product replaces the coarser factor 2 to the number of shifts. -/
theorem rawApply_row_weighted_bound (ds : List ℕ) (d n : ℕ) (hd : 2 ≤ d) :
    |rawApply ds (geometricRowTail d) n| ≤
      2 * weightedProduct ds (rate d) / rate d ^ n := by
  have hr (m : ℕ) : |geometricRowTail d m| ≤ 2 / rate d ^ m := by
    simpa [rawApply] using rawApply_row_bound [] d m hd (by simp)
  simpa [mul_comm] using rawApply_weighted_bound ds (geometricRowTail d)
    (rate d) 2 (rate_pos d) (by norm_num) hr n

/-- A full-power bound, using d/3 rather than sqrt d as a lower bound for the rate. -/
theorem rawApply_row_bound_third (ds : List ℕ) (d n : ℕ) (hd : 2 ≤ d)
    (hds : ∀ k ∈ ds, k ≤ d) :
    |rawApply ds (geometricRowTail d) n| ≤
      (2 ^ (ds.length + 1) * 3 ^ n) / (d : ℝ) ^ n := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hp : ((d : ℝ) / 3) ^ n ≤ rate d ^ n :=
    pow_le_pow_left₀ (by positivity) (rate_lower_third d (by omega)) n
  calc
    _ ≤ 2 ^ (ds.length + 1) / rate d ^ n := rawApply_row_bound ds d n hd hds
    _ ≤ 2 ^ (ds.length + 1) / ((d : ℝ) / 3) ^ n :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hp
    _ = _ := by rw [div_pow]; field_simp

/-- The full-power per-row estimate is summable for every n>=2. -/
theorem total_pseries_bound_third (ds : List ℕ) (K n : ℕ) (hn : 2 ≤ n)
    (hcancel : ∀ k < K, k + 2 ∈ ds)
    (hsize : ∀ k ∈ ds, k ≤ K + 2) :
    |rawApply ds (fun n => (∑' k : ℕ, term k) - (prefixQ n : ℝ)) n| ≤
      ∑' k : ℕ, (2 ^ (ds.length + 1) * 3 ^ n) / ((k + K + 2 : ℕ) : ℝ) ^ n := by
  rw [cutoff_tail_rows ds K n hcancel]
  have hs := summable_bound (2 ^ (ds.length + 1) * 3 ^ n) K n (by omega)
  have h := tsum_of_norm_bounded
    (f := fun k => rawApply ds (geometricRowTail (k + K + 2)) n) hs.hasSum (fun k => by
    simpa only [Real.norm_eq_abs] using rawApply_row_bound_third ds (k + K + 2) n
      (by omega) (fun j hj => (hsize j hj).trans (by omega)))
  simpa only [Real.norm_eq_abs] using h

/-- An explicit improvement of the earlier exponent floor(n/2)-1 to n-1,
at the cost of the factor 3^n. Nonvanishing is still not supplied. -/
theorem range_operator_explicit_bound_third (K n : ℕ) (hn : 2 ≤ n) :
    |rawApply (List.range' 2 K)
      (fun n => (∑' k : ℕ, term k) - (prefixQ n : ℝ)) n| ≤
      (2 ^ (K + 1) * 3 ^ n) / ((K + 1 : ℕ) : ℝ) ^ (n - 1) := by
  have hc : ∀ k < K, k + 2 ∈ List.range' 2 K := by
    intro k hk
    exact List.mem_range'.mpr ⟨k, hk, by omega⟩
  have hs : ∀ k ∈ List.range' 2 K, k ≤ K + 2 := by
    intro k hk
    obtain ⟨i, hi, he⟩ := List.mem_range'.mp hk
    omega
  calc
    _ ≤ ∑' k : ℕ, (2 ^ (K + 1) * 3 ^ n) / ((k + K + 2 : ℕ) : ℝ) ^ n := by
      simpa only [List.length_range'] using
        total_pseries_bound_third (List.range' 2 K) K n hn hc hs
    _ = (2 ^ (K + 1) * 3 ^ n) *
        (∑' k : ℕ, 1 / ((k + K + 2 : ℕ) : ℝ) ^ n) := by
      simp only [div_eq_mul_inv, one_mul, tsum_mul_left]
    _ ≤ (2 ^ (K + 1) * 3 ^ n) * (1 / ((K + 1 : ℕ) : ℝ) ^ (n - 1)) :=
      mul_le_mul_of_nonneg_left (pseries_tail_bound K n hn) (by positivity)
    _ = _ := by ring

end LambertSharperOperatorBounds

#print axioms LambertSharperOperatorBounds.rawApply_row_weighted_bound
#print axioms LambertSharperOperatorBounds.range_operator_explicit_bound_third
