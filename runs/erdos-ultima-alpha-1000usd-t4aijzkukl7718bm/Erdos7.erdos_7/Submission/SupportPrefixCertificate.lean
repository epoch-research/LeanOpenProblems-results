import Submission.SupportPrefixChecks
import Submission.SupportScheduledBudget

/-! Exact prefix and tail certificate for cofactor support at most two.
This is not yet the unrestricted odd covering conjecture. -/
namespace Erdos7SupportPrefixCertificate
open scoped BigOperators
open Erdos7SupportPrefixData Erdos7SupportPrefixChecks Erdos7SupportPrefixMetadata
open Erdos7SupportPrefixPotential Erdos7SupportPrefixInterpretation
open Erdos7SupportScheduledBudget Erdos7SupportCompression Erdos7SupportTailIteration
open Erdos7CompressionSieve
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 200000

lemma integer_margin : totalCost*25*(243*momentScale*1000^2)+tailNumerator 167*25*costScale <
    24*costScale*(243*momentScale*1000^2) := by
  simpa only [totalCost,tailNumerator,momNat,stageCount,cutoff,mul_assoc] using final_margin

theorem prefix_certificate (E : Fin 167 → ℕ) (μ : ℕ → TripleState →₀ ℚ)
    (hE : ∀ i,12 < E i) (hzero : μ 0=tripleInitial)
    (hstep : ∀ i : Fin 167,μ (i.val+1)=tripleStep (E i) (powerTail (p i) (cap i) (E i)) (μ i)) :
    prefixLoss μ+pairExpect (μ 167) statePotential/(1000:ℚ)^2 < 24/25 :=
  prefix_with_tail E μ hE hzero hstep all_lower_rows all_moment_rows all_loss_rows integer_margin

/-- A uniform finite-law budget, without numerical hypotheses remaining. -/
theorem budget_bound (N : ℕ) (P E : ℕ → ℕ) (C : ℕ → ℚ) (hs : Schedule N P E C) :
    supportCost (fun i : Fin N => E i) (fun i => powerTail (P i) (C i) (E i))
      (fun i => C i) (fun i => 1/((P i:ℚ)-1)) 2 < 24/25 :=
  scheduled_budget N P E C hs all_lower_rows all_moment_rows all_loss_rows integer_margin

#print axioms prefix_certificate
#print axioms budget_bound
end Erdos7SupportPrefixCertificate
