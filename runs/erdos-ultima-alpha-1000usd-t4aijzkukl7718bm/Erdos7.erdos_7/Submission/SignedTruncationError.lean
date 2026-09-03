import FormalConjecturesUtil

/-! Safe truncation of a signed comparison law represented as a difference
of positive laws. These inequalities alone do not establish a covering criterion. -/
namespace Erdos7SignedTruncationError
open scoped BigOperators

/-- Both positive components can be truncated, but only the omitted positive
component needs an upper-error charge when the test is nonnegative. -/
theorem signed_test_upper {Ω : Type*} [Fintype Ω]
    (P N D E φ : Ω → ℚ) (T : ℚ)
    (hD : ∀ x, D x ≤ P x) (hE : ∀ x, E x ≤ N x)
    (hφ0 : ∀ x, 0 ≤ φ x) (hφT : ∀ x, φ x ≤ T) :
    (∑ x, (P x-N x)*φ x) ≤
      (∑ x, (D x-E x)*φ x) + T*((∑ x, P x)-(∑ x, D x)) := by
  have hp (x : Ω) : (P x-N x)*φ x ≤
      (D x-E x)*φ x + T*(P x-D x) := by
    have h1 := mul_le_mul_of_nonneg_left (hφT x) (sub_nonneg.mpr (hD x))
    have h2 := mul_nonneg (sub_nonneg.mpr (hE x)) (hφ0 x)
    nlinarith
  calc
    _ ≤ ∑ x, ((D x-E x)*φ x + T*(P x-D x)) :=
      Finset.sum_le_sum (fun x _ => hp x)
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]

lemma hinge_identity (z t : ℚ) :
    max 0 (z-t) = z-t+max 0 (t-z) := by
  by_cases h : t ≤ z
  · rw [max_eq_right (sub_nonneg.mpr h), max_eq_left (sub_nonpos.mpr h)]
    ring
  · have h' := le_of_lt (lt_of_not_ge h)
    rw [max_eq_left (sub_nonpos.mpr h'), max_eq_right (sub_nonneg.mpr h')]
    ring

/-- Signed hinge loss from its signed mean and mass, lower sublaws, and the
explicit positive omitted-mass correction. No pointwise inequality has been
integrated against a signed weight. -/
theorem signed_hinge_upper {Ω : Type*} [Fintype Ω]
    (P N D E z : Ω → ℚ) (t : ℚ) (ht : 0 ≤ t)
    (hz : ∀ x, 0 ≤ z x)
    (hD : ∀ x, D x ≤ P x) (hE : ∀ x, E x ≤ N x) :
    (∑ x, (P x-N x)*max 0 (z x-t)) ≤
      (∑ x, (P x-N x)*z x) - t*(∑ x, (P x-N x)) +
      (∑ x, (D x-E x)*max 0 (t-z x)) +
      t*((∑ x, P x)-(∑ x, D x)) := by
  have htest := signed_test_upper P N D E (fun x => max 0 (t-z x)) t
    hD hE (fun _ => le_max_left _ _)
    (fun x => max_le ht (sub_le_self _ (hz x)))
  have heq : (∑ x, (P x-N x)*max 0 (z x-t)) =
      (∑ x, (P x-N x)*z x) - t*(∑ x, (P x-N x)) +
      (∑ x, (P x-N x)*max 0 (t-z x)) := by
    calc
      _ = ∑ x, ((P x-N x)*z x - t*(P x-N x) +
          (P x-N x)*max 0 (t-z x)) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [hinge_identity]
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [heq]
  linarith

#print axioms signed_test_upper
#print axioms signed_hinge_upper
end Erdos7SignedTruncationError
