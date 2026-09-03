import Submission.SuccessorTypeIDivisibility

/-! Expanded-output and permitted-axiom checks for the Type I bridge. -/
open Nat Finset ArithmeticFunction
open scoped BigOperators
open Erdos821.AnalyticSieve
open Erdos821.AnalyticSieve.SuccessorVaughan

example (P A B : Finset ℕ) (d T : ℕ) :
    (∑ n ∈ Icc 1 T with d ∣ n,
      (((P ×ˢ (A ×ˢ B)).filter (fun z => z.1*z.2.1*z.2.2+1=n)).card : ℝ)) =
    (((P ×ˢ (A ×ˢ B)).filter (fun z =>
      z.1*z.2.1*z.2.2+1 ≤ T ∧ d ∣ z.1*z.2.1*z.2.2+1)).card : ℝ) :=
  rectangle_divisible_output_prefix P A B d T

example (w v : ℕ → ℝ) (N U V : ℕ) (hU : 1 ≤ U)
    (B : ℝ) (hB0 : 0 ≤ B) (hB : ∀ n ∈ Icc 1 N, |w n-v n| ≤ B) :
    successorTypeIError w v N U V ≤ (U : ℝ)*B*Real.log N+
      3*Real.log N*(∑ d ∈ Icc 1 (U*V), outputMaxPrefix (fun n => w n-v n) d N) :=
  successorTypeIError_le_bounded_divisor_error w v N U V hU B hB0 hB

#print axioms divisibleOutputPrefix_eq_multiples
#print axioms outputPrefixSelector_spec
#print axioms outputMaxPrefix_nonneg
#print axioms divisibleOutputPrefix_le_max
#print axioms multiples_prefix_le_max
#print axioms abs_monotone_weighted_sum_le
#print axioms log_multiples_sum_le_max
#print axioms hyperbolicSum_quotient
#print axioms hyperbolicSum_supported_le
#print axioms outputDivisorError_nonneg
#print axioms outputDivisorError_mono
#print axioms successor_mu_log_le_divisor_error
#print axioms successor_typeI_zeta_le_divisor_error
#print axioms successorTypeIError_le_divisor_error
#print axioms weighted_short_sum_le
#print axioms successorTypeIError_le_bounded_divisor_error
#print axioms rectangle_divisible_output_prefix
#print axioms prime_output_card_gt_of_divisibility_gram
