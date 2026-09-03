import Submission.LambertBoundaryClearing
import Submission.LambertTotalBounds
import Submission.BoundaryPigeonhole

/-! A verified small-or-zero integral form construction. Nonvanishing or
independence of the resulting coefficient pairs is NOT proved. -/
namespace LambertBoundaryForms

open Finset Erdos68Development LambertDifferenceOperators LambertRawBounds
  LambertBoundaryClearing LambertTotalBounds BoundaryPigeonhole

def coefficient (ds : List ℕ) : ℤ :=
  (ds.map (fun d => (d.factorial : ℤ) - 1)).prod

lemma rawApply_sub (ds : List ℕ) (r s : ℕ → ℝ) :
    rawApply ds (fun n => r n - s n) = fun n => rawApply ds r n - rawApply ds s n := by
  induction ds generalizing r s with
  | nil => rfl
  | cons d ds ih =>
    have hs : rawShift d (fun n => r n - s n) =
        fun n => rawShift d r n - rawShift d s n := by
      funext n
      simp only [rawShift]
      ring
    rw [rawApply, hs, ih]
    rfl

lemma rawApply_const (ds : List ℕ) (x : ℝ) (n : ℕ) :
    rawApply ds (fun _ => x) n = (coefficient ds : ℝ) * x := by
  induction ds generalizing x with
  | nil => simp [rawApply, coefficient]
  | cons d ds ih =>
    have hs : rawShift d (fun _ => x) = fun _ => ((d.factorial : ℝ) - 1) * x := by
      funext n
      simp only [rawShift]
      ring
    rw [rawApply, hs, ih]
    simp only [coefficient, List.map_cons, List.prod_cons, Int.cast_mul,
      Int.cast_sub, Int.cast_natCast, Int.cast_one]
    ring

lemma form_identity (ds : List ℕ) (x : ℝ) (n : ℕ) :
    rawApply ds (fun n => x - (prefixQ n : ℝ)) n =
      (coefficient ds : ℝ) * x - (boundary ds n : ℝ) := by
  rw [rawApply_sub]
  dsimp only
  rw [rawApply_const, boundary_cast]

lemma window_error_bound (K H n : ℕ) (hH : 4 ≤ H) (hn : H ≤ n) :
    |(coefficient (List.range' 2 K) : ℝ) * (∑' k : ℕ, term k) -
        (boundary (List.range' 2 K) n : ℝ)| ≤
      2 ^ (K + 1) / ((K + 1 : ℕ) : ℝ) ^ (H / 2 - 1) := by
  rw [← form_identity]
  calc
    _ ≤ 2 ^ (K + 1) / ((K + 1 : ℕ) : ℝ) ^ (n / 2 - 1) :=
      range_operator_explicit_bound K n (by omega)
    _ ≤ _ := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      apply pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ K + 1 by omega))
      omega

/-- Pigeonholing the common boundary classes produces bounded nonzero
weights and a small integer form, possibly with zero coefficients or value. -/
theorem window_small_or_zero_form (K H D Q : ℕ) (hH : 4 ≤ H)
    (hcard : commonMultiplier (List.range' 2 K) (H + (D - 1)) < (Q + 1) ^ D) :
    ∃ w : Fin D → ℤ, w ≠ 0 ∧ (∀ i, |w i| ≤ Q) ∧ ∃ b : ℤ,
      (∑ i, (w i : ℝ) * (boundary (List.range' 2 K) (H + i) : ℝ)) = b ∧
      |(coefficient (List.range' 2 K) * ∑ i, w i : ℤ) *
        (∑' k : ℕ, term k) - b| ≤
        D * Q * (2 ^ (K + 1) / ((K + 1 : ℕ) : ℝ) ^ (H / 2 - 1)) := by
  apply small_integral_form D (commonMultiplier (List.range' 2 K) (H + (D - 1))) Q
    (commonMultiplier_pos _ _) hcard
  · intro i
    rw [boundary_cast]
    apply commonMultiplier_boundary_integral
    have hi := i.isLt
    omega
  · intro i
    exact window_error_bound K H (H + i) hH (by omega)

end LambertBoundaryForms

#print axioms LambertBoundaryForms.form_identity
#print axioms LambertBoundaryForms.window_small_or_zero_form
