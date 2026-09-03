import Submission.SuccessorProgressionBaseline

/-! Expanded-prefix and permitted-axiom checks for the concrete baseline. -/
open Nat Finset ArithmeticFunction
open scoped Classical BigOperators
open Erdos821.AnalyticSieve
open Erdos821.AnalyticSieve.SuccessorVaughan

example (m d T : ℕ) (hm : 0 < m) (hd : 0 < d) :
    |∑ n ∈ Icc 1 T with d ∣ n,
      ((if (n : ZMod m)=1 then (1 : ℝ) else 0)-
       (if n.Coprime m then 1/(m.totient : ℝ) else 0))| ≤
    1+(3 : ℝ)^m.primeFactors.card/(m.totient : ℝ) :=
  progression_divisible_prefix_error m d T hm hd

example : ∃ C : ℝ, 0 < C ∧ ∀ P : Finset ℕ, (∀ m ∈ P, 0 < m) →
    ∀ N U V : ℕ, 1 ≤ U →
    successorTypeIError (successorProgressionWeight P) (successorProgressionPrincipal P) N U V ≤
      (U : ℝ)*P.card*Real.log N+3*C*((U*V : ℕ) : ℝ)*P.card*Real.log N :=
  exists_uniform_progression_pool_TypeI_bound

example (P : Finset ℕ) (N : ℕ) (hP : ∀ m ∈ P, 0 < m ∧ m ≤ N) :
    (mangoldtSum N-(Nat.log 2 N : ℝ)*Real.log N)*(∑ m ∈ P, 1/(m.totient : ℝ)) ≤
      ∑ n ∈ Icc 1 N, vonMangoldt n*successorProgressionPrincipal P n :=
  progression_principal_mangoldt_lower P N hP

example (P : Finset ℕ) (N Y n : ℕ)
    (hP : ∀ m ∈ P, m ∈ Nat.smoothNumbers Y ∧ N ≤ m*Y)
    (hn : n ∈ (Icc 1 N).filter (fun n => n.Prime ∧ 0 < successorProgressionWeight P n)) :
    n.Prime ∧ n ≤ N ∧ n-1 ∈ Nat.smoothNumbers Y :=
  progression_prime_output_smooth P N Y n hP hn

#print axioms progressionPrefixCost_nonneg
#print axioms residueOneOutput_mul_eq_zero
#print axioms principalUnitOutput_mul_eq_zero
#print axioms principalUnitOutput_multiples
#print axioms principalUnitOutput_multiples_error
#print axioms residueOneOutput_multiples_error
#print axioms progression_divisible_prefix_error
#print axioms progression_outputMaxPrefix_le
#print axioms residueOneOutput_bounds
#print axioms principalUnitOutput_bounds
#print axioms progression_pointwise_difference_le
#print axioms divisibleOutputPrefix_remove_one
#print axioms remove_one_progression_prefix_error
#print axioms progressionPoolPrefixCost_nonneg
#print axioms progression_pool_prefix_error
#print axioms progression_pool_max_prefix_error
#print axioms progression_pool_divisor_error
#print axioms progression_pool_pointwise_difference_le
#print axioms progression_pool_TypeI_bound
#print axioms exists_uniform_progression_pool_prefix_constant
#print axioms exists_uniform_progression_pool_TypeI_bound
#print axioms weighted_mangoldt_remove_one
#print axioms weighted_principalUnitOutput
#print axioms progression_principal_mangoldt_eq
#print axioms progression_principal_mangoldt_lower
#print axioms successorProgressionWeight_one
#print axioms successorProgressionWeight_nonneg
#print axioms successorProgressionWeight_card
#print axioms successorProgressionWeight_le_divisors
#print axioms progression_prime_output_smooth
