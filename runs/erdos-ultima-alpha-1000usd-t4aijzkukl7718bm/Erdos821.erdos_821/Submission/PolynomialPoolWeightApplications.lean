import Submission.PolynomialPoolWeight
import Submission.RecordGcdMomentsApplications

/-!
# Polynomial-size restricted fibers have superquadratic pool weight

The source multiplicity exponent is unchanged. The new feature is a stronger
necessary lower bound on every containing input-prime pool.
-/

open Nat Filter
open scoped Classical BigOperators Topology
namespace Erdos821.CoprimeRecords
open LogarithmicOverlap

/-- The pool bound holds at arbitrarily large polynomial-size fibers, with
any fixed prime exclusion. No normalized-record assumption is required. -/
theorem exists_large_fiber_with_polynomial_pool_bound
    (K : ℕ) (hK : 0 < K) (C α β : ℝ) (hC : 0 ≤ C)
    (hα : 0 < α) (hαupper : α < 2041/4001) (hβ : 0 < β)
    (hβα : β*(1-α) < 1) (N : ℕ) :
    ∃ n : ℕ, max N 1 < n ∧ (n : ℝ)^α < (gAvoiding K n : ℝ) ∧
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) →
        (∀ a ∈ avoidingFiber K n, a.primeFactors ⊆ P) →
        C*(Real.log (n : ℝ))^β < poolWeight P := by
  have hα1 : α < 1 := by linarith
  obtain ⟨M, hM⟩ := eventually_atTop.mp
    (eventually_large_fiber_requires_polynomial_pool C α β hC hα hα1 hβ hβα)
  have H := infinite_gAvoiding_independent_range K hK α hα hαupper
  obtain ⟨n, hn, hnlarge⟩ := H.exists_gt (max M (max N 1))
  refine ⟨n, (le_max_right _ _).trans_lt hnlarge, hn.2, ?_⟩
  intro P hP hcut
  apply hM n ((le_max_left _ _).trans hnlarge.le) (avoidingFiber K n) P hP
    (fun a ha => ⟨(mem_avoidingFiber.mp ha).2.2, hcut a ha⟩)
  simpa only [avoidingFiber_card] using hn.2

/-- An explicit superquadratic logarithmic power, using an attained
multiplicity exponent of 51/100. This does not increase that exponent. -/
theorem exists_large_fiber_with_superquadratic_pool_bound
    (K : ℕ) (hK : 0 < K) (C : ℝ) (hC : 0 ≤ C) (N : ℕ) :
    ∃ n : ℕ, max N 1 < n ∧ (n : ℝ)^(51/100 : ℝ) < (gAvoiding K n : ℝ) ∧
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) →
        (∀ a ∈ avoidingFiber K n, a.primeFactors ⊆ P) →
        C*(Real.log (n : ℝ))^(51/25 : ℝ) < poolWeight P := by
  exact exists_large_fiber_with_polynomial_pool_bound K hK C (51/100) (51/25)
    hC (by norm_num) (by norm_num) (by norm_num) (by norm_num) N

end Erdos821.CoprimeRecords
