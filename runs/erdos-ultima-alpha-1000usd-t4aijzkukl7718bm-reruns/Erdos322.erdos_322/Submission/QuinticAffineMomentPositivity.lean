import FormalConjecturesUtil

/-!
A positivity obstruction for the affine-power construction
`(1 - A*t^5)^5 + t^5 * ∑ i, (b i + c i*t^5)^5 = 1`.
This file does not assert an upper bound for unrestricted representations.
-/
namespace Erdos322Research.QuinticAffineMomentPositivity

open Finset

/-- An exact sum-of-squares identity for the five required moments. -/
theorem square_certificate {ι : Type*} [Fintype ι] (A : ℝ) (b c : ι → ℝ)
    (h0 : ∑ i, b i ^ 5 = 5*A)
    (h1 : ∑ i, b i ^ 4*c i = -2*A^2)
    (h2 : ∑ i, b i ^ 3*c i^2 = A^3)
    (h3 : ∑ i, b i ^ 2*c i^3 = -A^4/2)
    (h4 : ∑ i, b i*c i^4 = A^5/5) :
    ∑ i, b i * (10*c i^2 + A*b i*c i - 2*A^2*b i^2)^2 = -A^5 := by
  have he (i : ι) :
      b i * (10*c i^2 + A*b i*c i - 2*A^2*b i^2)^2 =
        100*(b i*c i^4) + 20*A*(b i^2*c i^3) -
          39*A^2*(b i^3*c i^2) - 4*A^3*(b i^4*c i) +
          4*A^4*(b i^5) := by ring
  simp only [he, sum_add_distrib, sum_sub_distrib, ← mul_sum]
  rw [h0, h1, h2, h3, h4]
  ring

/-- Nonnegative initial slopes cannot satisfy the quintic affine moment
conditions with nonzero scale. The number of affine forms is arbitrary. -/
theorem no_nonnegative_initial_slopes {ι : Type*} [Fintype ι]
    (A : ℝ) (b c : ι → ℝ) (hA : A ≠ 0) (hb : ∀ i, 0 ≤ b i)
    (h0 : ∑ i, b i ^ 5 = 5*A)
    (h1 : ∑ i, b i ^ 4*c i = -2*A^2)
    (h2 : ∑ i, b i ^ 3*c i^2 = A^3)
    (h3 : ∑ i, b i ^ 2*c i^3 = -A^4/2)
    (h4 : ∑ i, b i*c i^4 = A^5/5) : False := by
  have hsum : 0 ≤ ∑ i, b i^5 := sum_nonneg (fun i _ => pow_nonneg (hb i) _)
  have hpos : 0 < A := by rw [h0] at hsum; rcases lt_or_gt_of_ne hA with h | h <;> linarith
  have hsq : 0 ≤ ∑ i, b i * (10*c i^2 + A*b i*c i - 2*A^2*b i^2)^2 :=
    sum_nonneg (fun i _ => mul_nonneg (hb i) (sq_nonneg _))
  rw [square_certificate A b c h0 h1 h2 h3 h4] at hsq
  have hp := pow_pos hpos 5
  linarith

open Polynomial

private noncomputable def affineFifth (b c : ℝ) : Polynomial ℝ := (C c * X + C b)^5

private theorem affineFifth_coeff (b c : ℝ) (j : ℕ) :
    (affineFifth b c).coeff j = (Nat.choose 5 j : ℝ) * (b^(5-j)*c^j) := by
  have he : affineFifth b c = ((X + C b)^5).comp (C c * X) := by
    simp [affineFifth]
  rw [he, comp_C_mul_X_coeff, coeff_X_add_C_pow]
  ring

/-- The pointwise affine identity is impossible if all constant terms of
its affine forms are nonnegative. No restriction on the number of terms is
needed. This only addresses this polynomial construction. -/
theorem no_nonnegative_affine_identity {ι : Type*} [Fintype ι]
    (A : ℝ) (b c : ι → ℝ) (hA : A ≠ 0) (hb : ∀ i, 0 ≤ b i) :
    ¬ (∀ z : ℝ, (1-A*z)^5 + z * ∑ i, (b i+c i*z)^5 = 1) := by
  intro hid
  have hp : affineFifth 1 (-A) + X * ∑ i, affineFifth (b i) (c i) = 1 := by
    apply Polynomial.funext
    intro z
    simpa [affineFifth, eval_finset_sum, sub_eq_add_neg, add_comm] using hid z
  have hc (j : ℕ) :
      (affineFifth 1 (-A)).coeff (j+1) +
        ∑ i, (affineFifth (b i) (c i)).coeff j = 0 := by
    have h := congrArg (fun P : Polynomial ℝ => P.coeff (j+1)) hp
    simpa only [coeff_add, coeff_X_mul, finset_sum_coeff, coeff_one,
      Nat.add_one_ne_zero, ↓reduceIte] using h
  have h0 := hc 0
  have h1 := hc 1
  have h2 := hc 2
  have h3 := hc 3
  have h4 := hc 4
  norm_num [affineFifth_coeff, Nat.choose, ← Finset.mul_sum] at h0 h1 h2 h3 h4
  apply no_nonnegative_initial_slopes A b c hA hb
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith

end Erdos322Research.QuinticAffineMomentPositivity
