import Submission.FirstHitTransfer
import Submission.FirstHitSharpCost

/-! Reference first-hit certificates with their actual coefficient costs.
This is a conditional certificate, not the quadratic Jacobsthal theorem. -/
namespace Erdos970.FiniteSelberg
open Finset Real
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma ordinaryCoefficient_canonical_eq (q : ι → ℝ) (D : Finset (Finset ι))
    (T : Finset ι) : ordinaryCoefficient q (canonicalOrthogonal q D) T =
      coefficient q D T := by
  classical
  unfold ordinaryCoefficient canonicalOrthogonal coefficient
  have he (Q : Finset ι) :
      (if T ⊆ Q then weight q Q * (if Q ∈ D then 1 / normalizer q D else 0) else 0) =
      if Q ∈ D then (if T ⊆ Q then weight q Q else 0) / normalizer q D else 0 := by
    split_ifs <;> ring
  simp_rw [he]
  simp only [sum_ite_mem, univ_inter, ← sum_div]
  ring

lemma coefficient_abs_sum_eq_kernelCost (q : ι → ℝ) (D : Finset (Finset ι))
    (hD : ∀ A ∈ D, ∀ B ⊆ A, B ∈ D) :
    (∑ T ∈ D, |coefficient q D T|) = kernelCost q (canonicalOrthogonal q D) := by
  unfold kernelCost
  simp_rw [ordinaryCoefficient_canonical_eq]
  exact sum_subset (subset_univ D) (fun T _ hT => by
    rw [coefficient_eq_zero_of_not_mem q D hD T hT, abs_zero])

lemma firstHitCoefficient_cost_eq (q : ι → ℝ) (D : ι → Finset (Finset ι))
    (hD : ∀ i, ∀ A ∈ D i, ∀ B ⊆ A, B ∈ D i) :
    (∑ t : FirstHitTerm ι, |firstHitCoefficient q D t|) =
      1 + ∑ i, kernelCost q (canonicalOrthogonal q (D i)) ^ 2 := by
  simp only [Fintype.sum_option, Fintype.sum_prod_type, firstHitCoefficient, abs_one,
    apply_ite abs, abs_zero, abs_neg]
  simp only [sum_ite_irrel, sum_ite_mem, univ_inter, sum_const_zero, abs_mul]
  congr 1
  apply sum_congr rfl
  intro i _
  rw [← sum_mul_sum, coefficient_abs_sum_eq_kernelCost q (D i) (hD i), pow_two]

section Ordered
variable [LinearOrder ι]

/-- Marginal domination retains the exact reference L1 cost, rather than
replacing every ordinary coefficient by one. -/
theorem survivor_of_dominating_first_hit_cost (q q' : ι → ℝ)
    (hq : ∀ i, q i < 1 ∧ q i ≤ q' i ∧ q' i ≤ 1)
    (hq' : ∀ i, 0 < q' i ∧ q' i < 1)
    (D : ι → Finset (Finset ι)) (hDn : ∀ i, (D i).Nonempty)
    (hD : ∀ i, ∀ A ∈ D i, ∀ B ⊆ A, B ∈ D i)
    (hprior : ∀ i, ∀ Q ∈ D i, ∀ j ∈ Q, j < i)
    (m : ℕ) (ω : ℕ → ι → Bool)
    (herr : ∀ T : Finset ι,
      |(∑ j ∈ range m, hitMonomial T (ω j)) - (m : ℝ) * ∏ i ∈ T, q i| ≤ 1)
    (hmain : (m : ℝ) * (∑ i, q' i / normalizer q' (D i)) +
      1 + (∑ i, kernelCost q' (canonicalOrthogonal q' (D i)) ^ 2) < m) :
    ∃ j < m, ∀ i, ω j i = false := by
  apply survivor_from_dominating_moments univ (firstHitCoefficient q' D)
    firstHitTermSupport q q' hq m ω herr
  · intro v hv
    rw [firstHitCoefficient_value q' D hD]
    linarith [first_hit_sum_ge_one q' hq' D hDn hprior v hv]
  · rw [firstHitCoefficient_mean q' hq' D hDn hD hprior,
      firstHitCoefficient_cost_eq q' D hD]
    linarith

end Ordered
#print axioms survivor_of_dominating_first_hit_cost
end Erdos970.FiniteSelberg
