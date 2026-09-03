import FormalConjecturesUtil

/-! Reciprocal summability for nonnegative sequences with sublinear
power bounds on their partial sums. -/
namespace Erdos972ReciprocalPrefixSummability

open Finset

lemma reciprocal_succ_difference (n : ℕ) :
    (1 / ((n + 1 : ℕ) : ℝ) - 1 / ((n + 2 : ℕ) : ℝ)) =
      1 / (((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ)) := by
  have h1 : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have h2 : ((n + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp
  push_cast
  ring

/-- The exponent is strictly below one; no pointwise bound on the sequence
itself is assumed. -/
theorem summable_div_succ_of_prefix_rpow {a : ℕ → ℝ} {C s : ℝ}
    (ha : ∀ n, 0 ≤ a n) (hC : 0 ≤ C) (hs : s < 1)
    (hprefix : ∀ n : ℕ, ∑ k ∈ range (n+1), a k ≤ C * ((n+1 : ℕ) : ℝ)^s) :
    Summable (fun n : ℕ => a n / ((n+1 : ℕ) : ℝ)) := by
  have hseries : Summable (fun n : ℕ => ((n+1 : ℕ) : ℝ)^(s-2)) := by
    exact (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by linarith))
  let H : ℝ := ∑' n : ℕ, ((n+1 : ℕ) : ℝ)^(s-2)
  have hH : 0 ≤ H := tsum_nonneg fun n => Real.rpow_nonneg (by positivity) _
  apply summable_of_sum_range_norm_le (c := C + C*H)
  intro N
  have hnonneg (k : ℕ) : 0 ≤ a k / ((k+1:ℕ):ℝ) := div_nonneg (ha k) (by positivity)
  simp_rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg _)]
  cases N with
  | zero => simp only [range_zero, sum_empty]; positivity
  | succ n =>
    have hparts := sum_range_by_parts
      (fun k : ℕ => (1:ℝ)/((k+1:ℕ):ℝ)) a (n+1)
    simp only [add_tsub_cancel_right, smul_eq_mul, one_div_mul_eq_div] at hparts
    have hrewrite :
        (∑ k ∈ range (n+1), a k / ((k+1:ℕ):ℝ)) =
          (∑ k ∈ range (n+1), a k) / ((n+1:ℕ):ℝ) +
            ∑ k ∈ range n, (∑ j ∈ range (k+1), a j) /
              (((k+1:ℕ):ℝ)*((k+2:ℕ):ℝ)) := by
      rw [hparts, sub_eq_add_neg, ← sum_neg_distrib]
      congr 1
      apply sum_congr rfl
      intro k hk
      rw [← neg_mul, neg_sub, reciprocal_succ_difference]
      rw [one_div_mul_eq_div]
    rw [hrewrite]
    have hn1 : (1:ℝ) ≤ ((n+1:ℕ):ℝ) := by exact_mod_cast Nat.succ_pos n
    have hn0 : (0:ℝ) < ((n+1:ℕ):ℝ) := by positivity
    have hb : (∑ k ∈ range (n+1), a k) / ((n+1:ℕ):ℝ) ≤ C := by
      apply (div_le_iff₀ hn0).mpr
      apply (hprefix n).trans
      apply mul_le_mul_of_nonneg_left _ hC
      simpa using Real.rpow_le_rpow_of_exponent_le hn1 hs.le
    have hterm (k : ℕ) : (∑ j ∈ range (k+1), a j) /
        (((k+1:ℕ):ℝ)*((k+2:ℕ):ℝ)) ≤ C * ((k+1:ℕ):ℝ)^(s-2) := by
      have hk : (0:ℝ) < ((k+1:ℕ):ℝ) := by positivity
      have hkk : (((k+1:ℕ):ℝ))^2 ≤ ((k+1:ℕ):ℝ)*((k+2:ℕ):ℝ) := by
        push_cast
        nlinarith
      calc
        _ ≤ (C * ((k+1:ℕ):ℝ)^s) /
            (((k+1:ℕ):ℝ)*((k+2:ℕ):ℝ)) :=
          div_le_div_of_nonneg_right (hprefix k) (by positivity)
        _ ≤ (C * ((k+1:ℕ):ℝ)^s) / (((k+1:ℕ):ℝ))^2 :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hkk
        _ = C * ((k+1:ℕ):ℝ)^(s-2) := by
          rw [Real.rpow_sub hk, Real.rpow_two, mul_div_assoc]
    calc
      _ ≤ C + ∑ k ∈ range n, C * ((k+1:ℕ):ℝ)^(s-2) :=
        add_le_add hb (sum_le_sum fun k _ => hterm k)
      _ = C + C * ∑ k ∈ range n, ((k+1:ℕ):ℝ)^(s-2) := by rw [mul_sum]
      _ ≤ C + C * H := by
        apply add_le_add le_rfl
        apply mul_le_mul_of_nonneg_left _ hC
        exact hseries.sum_le_tsum _ (fun k _ => Real.rpow_nonneg (by positivity) _)

#print axioms summable_div_succ_of_prefix_rpow

end Erdos972ReciprocalPrefixSummability
