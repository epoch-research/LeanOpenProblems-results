import Submission.SelbergEnergyCriterion
import Submission.SelbergPrimes

/-! Quantitative survivor counts from arbitrary lower kernels, retaining the
empty-pattern kernel value. This is stronger than the corresponding existence
criterion but does not assert positivity at a quadratic scale. -/
namespace Erdos970.FiniteSelberg
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma lowerKernel_le_empty_count (q : ι → ℝ) (c : Finset ι → ℝ) (ω : ι → Bool) :
    (1 - ∑ i, hitCoordinate i ω) * linearKernel q c ω ^ 2 ≤
      (∑ Q : Finset ι, c Q) ^ 2 * (if ω = (fun _ => false) then 1 else 0) := by
  classical
  by_cases he : ω = (fun _ => false)
  · subst ω
    simp [linearKernel, basis_at_empty, hitCoordinate]
  · simpa only [if_neg he, mul_zero] using lowerKernel_nonpos_of_nonempty q c ω he

/-- The error-corrected mean bounds the number of empty patterns after
multiplication by the squared value of the kernel at that pattern. -/
theorem survivor_count_lower_kernel (q : ι → ℝ) (hq : ∀ i, q i ≠ 0)
    (c : Finset ι → ℝ) (m : ℕ) (ω : ℕ → ι → Bool)
    (herr : ∀ T : Finset ι,
      |(∑ j ∈ range m, hitMonomial T (ω j)) - (m : ℝ) * ∏ i ∈ T, q i| ≤ 1) :
    (m : ℝ) * kernelEnergy q c - (Fintype.card ι + 1 : ℝ) * kernelCost q c ^ 2 ≤
      (∑ Q : Finset ι, c Q) ^ 2 * (((range m).filter (fun j => ∀ i, ω j i = false)).card : ℝ) := by
  classical
  have hlo := (abs_le.mp (arbitrary_lowerKernel_error q hq c m ω herr)).1
  have hhi := sum_le_sum (fun j (_ : j ∈ range m) => lowerKernel_le_empty_count q c (ω j))
  rw [← mul_sum] at hhi
  have hcount : (∑ j ∈ range m, if ω j = (fun _ => false) then (1 : ℝ) else 0) =
      (((range m).filter (fun j => ∀ i, ω j i = false)).card : ℝ) := by
    simp only [funext_iff, sum_boole]
  rw [hcount] at hhi
  linarith only [hlo, hhi]

/-- Specialization to genuine interval counts with distinct prime moduli. -/
theorem prime_survivor_count_lower_kernel (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (c : Finset ι → ℝ) (r : ℕ → ℕ) (m : ℕ) :
    (m : ℝ) * kernelEnergy (fun i => 1 / (p i : ℝ)) c -
      (Fintype.card ι + 1 : ℝ) * kernelCost (fun i => 1 / (p i : ℝ)) c ^ 2 ≤
      (∑ Q : Finset ι, c Q) ^ 2 *
        (((range m).filter (fun j => ∀ i, ¬j ≡ r (p i) [MOD p i])).card : ℝ) := by
  simpa only [decide_eq_false_iff_not] using survivor_count_lower_kernel
    (fun i => 1 / (p i : ℝ)) (fun i => by have := (hp i).pos; positivity) c m
    (fun j i => decide (j ≡ r (p i) [MOD p i])) (prime_hits_intersection_error p hp hinj r m)

#print axioms survivor_count_lower_kernel
#print axioms prime_survivor_count_lower_kernel
end Erdos970.FiniteSelberg
