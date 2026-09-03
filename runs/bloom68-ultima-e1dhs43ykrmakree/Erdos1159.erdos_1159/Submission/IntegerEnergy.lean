import FormalConjecturesUtil

/-!
# Exact recovery from integer energy

These elementary lemmas formalize an auxiliary arithmetic criterion used in
incidence inversion. They do not supply the missing positive-codeword energy
gap, and do not prove or disprove Erdős Problem 1159. This file does not import
`Submission.Spec` or either of its admitted theorems.
-/

open scoped BigOperators

namespace Erdos1159.IntegerEnergy

private lemma mul_pred_nonneg (z : ℤ) : 0 ≤ z * (z - 1) := by
  have hz : z ≤ 0 ∨ 1 ≤ z := by omega
  rcases hz with hz | hz
  · exact mul_nonneg_of_nonpos_of_nonpos hz (by omega)
  · exact mul_nonneg (by omega) (by omega)

private lemma two_le_mul_pred (z : ℤ) (h0 : z ≠ 0) (h1 : z ≠ 1) :
    2 ≤ z * (z - 1) := by
  have hz : z ≤ -1 ∨ 2 ≤ z := by omega
  rcases hz with hz | hz
  · nlinarith [sq_nonneg (z + 1)]
  · nlinarith [sq_nonneg (z - 2)]

variable {I : Type*} [Fintype I]

/-- The integer energy excess is always nonnegative. -/
theorem sum_sq_sub_sum_nonneg (w : I → ℤ) :
    0 ≤ (∑ i, w i ^ 2) - ∑ i, w i := by
  have h := Finset.sum_nonneg (s := Finset.univ)
    (fun i _ => mul_pred_nonneg (w i))
  have heq : (∑ i, w i * (w i - 1)) = (∑ i, w i ^ 2) - ∑ i, w i := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rwa [heq] at h

/-- Equality of the first and second integer moments forces Boolean entries. -/
theorem sum_sq_eq_sum_iff (w : I → ℤ) :
    (∑ i, w i ^ 2) = (∑ i, w i) ↔ ∀ i, w i = 0 ∨ w i = 1 := by
  classical
  have heq : (∑ i, w i * (w i - 1)) = (∑ i, w i ^ 2) - ∑ i, w i := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  constructor
  · intro h i
    have hi := Finset.single_le_sum (s := Finset.univ)
      (f := fun j => w j * (w j - 1))
      (fun j _ => mul_pred_nonneg (w j)) (Finset.mem_univ i)
    rw [heq, h, sub_self] at hi
    have hz : w i * (w i - 1) = 0 := le_antisymm hi (mul_pred_nonneg (w i))
    rcases mul_eq_zero.mp hz with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (by omega)
  · intro h
    apply Finset.sum_congr rfl
    intro i hi
    rcases h i with h0 | h1
    · simp [h0]
    · simp [h1]

/-- Any non-Boolean integer vector has an energy excess of at least two. -/
theorem two_le_sum_sq_sub_sum (w : I → ℤ)
    (h : ¬ ∀ i, w i = 0 ∨ w i = 1) :
    2 ≤ (∑ i, w i ^ 2) - ∑ i, w i := by
  classical
  push_neg at h
  obtain ⟨i, h0, h1⟩ := h
  have hi := Finset.single_le_sum (s := Finset.univ)
    (f := fun j => w j * (w j - 1))
    (fun j _ => mul_pred_nonneg (w j)) (Finset.mem_univ i)
  have heq : (∑ i, w i * (w i - 1)) = (∑ i, w i ^ 2) - ∑ i, w i := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [heq] at hi
  exact (two_le_mul_pred (w i) h0 h1).trans hi

/-- An incidence-type energy identity recovers a Boolean inverse exactly at equality.
The energy identity is an explicit hypothesis, not an assumed inverse theorem. -/
theorem recovery_iff (w : I → ℤ) (p e : ℤ) (hp : 0 < p)
    (he : e = p * (∑ i, w i ^ 2) + (∑ i, w i) ^ 2) :
    e = p * (∑ i, w i) + (∑ i, w i) ^ 2 ↔
      ∀ i, w i = 0 ∨ w i = 1 := by
  rw [he, ← sum_sq_eq_sum_iff]
  constructor
  · intro h
    have hm : p * (∑ i, w i ^ 2) = p * (∑ i, w i) := by linarith
    exact mul_left_cancel₀ (ne_of_gt hp) hm
  · intro h
    rw [h]

/-- The corresponding quantitative gap when the inverse is not Boolean. -/
theorem recovery_gap (w : I → ℤ) (p e : ℤ) (hp : 0 < p)
    (he : e = p * (∑ i, w i ^ 2) + (∑ i, w i) ^ 2)
    (h : ¬ ∀ i, w i = 0 ∨ w i = 1) :
    2 * p ≤ e - (p * (∑ i, w i) + (∑ i, w i) ^ 2) := by
  have hg := mul_le_mul_of_nonneg_left (two_le_sum_sq_sub_sum w h) (le_of_lt hp)
  rw [he]
  nlinarith only [hg]

end Erdos1159.IntegerEnergy

#print axioms Erdos1159.IntegerEnergy.sum_sq_sub_sum_nonneg
#print axioms Erdos1159.IntegerEnergy.sum_sq_eq_sum_iff
#print axioms Erdos1159.IntegerEnergy.two_le_sum_sq_sub_sum
#print axioms Erdos1159.IntegerEnergy.recovery_iff
#print axioms Erdos1159.IntegerEnergy.recovery_gap
