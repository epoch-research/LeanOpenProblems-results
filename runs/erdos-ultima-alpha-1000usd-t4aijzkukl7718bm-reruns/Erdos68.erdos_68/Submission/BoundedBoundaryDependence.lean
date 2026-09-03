import Submission.BoundaryPigeonhole

/-! A determinant obstruction for two small forms with a common retained
coefficient. These bounds assert dependence, not irrationality. -/

namespace BoundedBoundaryDependence

open Finset BoundaryPigeonhole

lemma common_coefficient_dependence (A s t b d : ℤ) (x L η : ℝ)
    (hL : 0 ≤ L)
    (hs : |(s : ℝ)| ≤ L) (ht : |(t : ℝ)| ≤ L)
    (hb : |((A*s : ℤ) : ℝ)*x-b| ≤ η)
    (hd : |((A*t : ℤ) : ℝ)*x-d| ≤ η)
    (hsmall : 2*L*η < 1) : s*d-b*t = 0 := by
  have hid : ((s*d-b*t : ℤ) : ℝ) =
      (t : ℝ)*(((A*s : ℤ) : ℝ)*x-b) -
        (s : ℝ)*(((A*t : ℤ) : ℝ)*x-d) := by push_cast; ring
  have he : |((s*d-b*t : ℤ) : ℝ)| ≤ 2*L*η := by
    rw [hid]
    calc
      _ ≤ |(t : ℝ)*(((A*s : ℤ) : ℝ)*x-b)| +
          |(s : ℝ)*(((A*t : ℤ) : ℝ)*x-d)| := abs_sub _ _
      _ = |(t : ℝ)| * |(((A*s : ℤ) : ℝ)*x-b)| +
          |(s : ℝ)| * |(((A*t : ℤ) : ℝ)*x-d)| := by rw [abs_mul, abs_mul]
      _ ≤ L*η + L*η := add_le_add
        (mul_le_mul ht hb (abs_nonneg _) hL)
        (mul_le_mul hs hd (abs_nonneg _) hL)
      _ = _ := by ring
  have hz : |s*d-b*t| < (1 : ℤ) := by exact_mod_cast he.trans_lt hsmall
  have hh := abs_lt.mp hz
  omega

lemma sum_weights_bound (D Q : ℕ) (w : Fin D → ℤ) (hw : ∀ i, |w i| ≤ Q) :
    |((∑ i, w i : ℤ) : ℝ)| ≤ (D : ℝ)*Q := by
  rw [Int.cast_sum]
  calc
    _ ≤ ∑ i, |(w i : ℝ)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin D, (Q : ℝ) := by
      apply sum_le_sum
      intro i _
      exact_mod_cast hw i
    _ = _ := by simp

/-- If 2*(D*Q)^2 times the row error is below one, every two integrally
cleared boundaries with these weight bounds have dependent coefficient pairs.
The retained coefficient A cancels out of the determinant bound. -/
theorem bounded_window_dependence (D Q : ℕ) (A : ℤ) (x η : ℝ)
    (B : Fin D → ℝ)
    (herror : ∀ i, |(A : ℝ)*x-B i| ≤ η)
    (hsmall : 2*((D : ℝ)*Q)*((D : ℝ)*Q*η) < 1)
    (w v : Fin D → ℤ) (hw : ∀ i, |w i| ≤ Q) (hv : ∀ i, |v i| ≤ Q)
    (b d : ℤ) (hb : ∑ i, (w i : ℝ)*B i = b) (hd : ∑ i, (v i : ℝ)*B i = d) :
    (∑ i, w i)*d - b*(∑ i, v i) = 0 := by
  have hwe := weighted_error_bound D Q x η A B w hw herror
  have hve := weighted_error_bound D Q x η A B v hv herror
  rw [hb] at hwe
  rw [hd] at hve
  exact common_coefficient_dependence A _ _ b d x ((D : ℝ)*Q) ((D : ℝ)*Q*η)
    (by positivity) (sum_weights_bound D Q w hw)
    (sum_weights_bound D Q v hv) hwe hve hsmall

/-- Independence requires a weight/error budget of at least one. -/
theorem independent_requires_large_weights (D Q : ℕ) (A : ℤ) (x η : ℝ)
    (B : Fin D → ℝ) (herror : ∀ i, |(A : ℝ)*x-B i| ≤ η)
    (w v : Fin D → ℤ) (hw : ∀ i, |w i| ≤ Q) (hv : ∀ i, |v i| ≤ Q)
    (b d : ℤ) (hb : ∑ i, (w i : ℝ)*B i = b) (hd : ∑ i, (v i : ℝ)*B i = d)
    (hind : (∑ i, w i)*d - b*(∑ i, v i) ≠ 0) :
    1 ≤ 2*((D : ℝ)*Q)*((D : ℝ)*Q*η) := by
  by_contra hn
  exact hind (bounded_window_dependence D Q A x η B herror (lt_of_not_ge hn)
    w v hw hv b d hb hd)

end BoundedBoundaryDependence

#print axioms BoundedBoundaryDependence.bounded_window_dependence

#print axioms BoundedBoundaryDependence.independent_requires_large_weights
