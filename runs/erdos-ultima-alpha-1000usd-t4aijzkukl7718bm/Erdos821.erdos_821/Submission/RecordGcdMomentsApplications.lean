import Submission.RecordGcdMoments
import Submission.IndependentCompositeGain

/-!
# Large restricted record fibers with uniform gcd moments

The independent-parameter exponent is preserved under fixed prime exclusion.
The resulting record fibers satisfy the uniform moment and support-weight
estimates. No multiplicity exponent larger than the source range is claimed.
-/

open Nat Filter
open scoped Classical BigOperators
namespace Erdos821

/-- The strongest current fixed exponent survives exclusion of any fixed
finite set of input primes. -/
theorem infinite_gAvoiding_independent_range (K : ℕ) (hK : 0 < K) (γ : ℝ)
    (hγ : 0 < γ) (hupper : γ < 2041/4001) :
    {n : ℕ | 0 < n ∧ (n : ℝ)^γ < (gAvoiding K n : ℝ)}.Infinite := by
  let α : ℝ := 2041/4001
  have hgap : 0 < (α-γ)/2 := by dsimp [α]; linarith
  apply infinite_gAvoiding_of_infinite_g K hK γ ((α-γ)/2) hγ hgap
  apply infinite_g_gt_independent_uniform
  change γ+(α-γ)/2 < α
  linarith

namespace CoprimeRecords
open LogarithmicOverlap

/-- The order and moment exponent are fixed before the record output grows. -/
theorem exists_large_records_with_gcd_moment_bound (K : ℕ) (hK : 0 < K)
    (α s t : ℝ) (hα : 0 < α) (hupper : α < 2041/4001) (hsα : s < α)
    (hst : 1 < 2*s-t) (N : ℕ) :
    ∃ n : ℕ, max N 1 < n ∧ (n : ℝ)^α < (gAvoiding K n : ℝ) ∧
      (∀ j : ℕ, j ≤ n → (gAvoiding K j : ℝ)/(j : ℝ)^s ≤
        (gAvoiding K n : ℝ)/(n : ℝ)^s) ∧
      gcdTotientMoment K n t ≤ (gAvoiding K n : ℝ)^2*recordGcdConstant s t := by
  have H := infinite_gAvoiding_independent_range K hK α hα hupper
  have H' : {n : ℕ | (n : ℝ)^α < (gAvoiding K n : ℝ)}.Infinite :=
    H.mono (fun n hn => hn.2)
  obtain ⟨n, hn, hg, hrec⟩ := exists_large_normalized_record_at
    (gAvoiding K) α s hsα H' (max N 1)
  exact ⟨n, hn, hg, hrec, record_gcd_totient_moment_le K n (by omega) s t hst hrec⟩

/-- Arbitrarily large polynomial-size fibers with positive uniform gcd
moments and the quadratic support-weight bound. All constants are independent
of the fixed prime-exclusion parameter K. -/
theorem exists_large_records_with_quadratic_pool_bound (α : ℝ)
    (hα : 1/2 < α) (hupper : α < 2041/4001) :
    ∃ s t C : ℝ, 1/2 < s ∧ s < α ∧ 0 < t ∧ 0 < C ∧
      ∀ K : ℕ, 0 < K → ∀ N : ℕ, ∃ n : ℕ,
        max N 1 < n ∧ (n : ℝ)^α < (gAvoiding K n : ℝ) ∧
        gcdTotientMoment K n t ≤ (gAvoiding K n : ℝ)^2*recordGcdConstant s t ∧
        ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) →
          (∀ a ∈ avoidingFiber K n, a.primeFactors ⊆ P) →
          (Real.log (n : ℝ))^2 ≤ C*poolWeight P := by
  let s := (α+1/2)/2
  let t := s-1/2
  have hs : 1/2 < s := by dsimp [s]; linarith
  have hsα : s < α := by dsimp [s]; linarith
  have ht : 0 < t := by dsimp [t]; linarith
  have hst : 1 < 2*s-t := by dsimp [t]; linarith
  obtain ⟨C, hC, hpool⟩ := exists_quadratic_record_pool_bound s hs
  refine ⟨s, t, C, hs, hsα, ht, hC, ?_⟩
  intro K hK N
  obtain ⟨n, hn, hg, hrec, hmoment⟩ := exists_large_records_with_gcd_moment_bound
    K hK α s t (by linarith) hupper hsα hst N
  have hn0 : 0 < n := by omega
  have hG : 0 < gAvoiding K n := by
    have hh : (0 : ℝ) < n := by exact_mod_cast hn0
    exact_mod_cast (Real.rpow_pos_of_pos hh α).trans hg
  exact ⟨n, hn, hg, hmoment, hpool K n hn0 hG hrec⟩

end CoprimeRecords
end Erdos821
