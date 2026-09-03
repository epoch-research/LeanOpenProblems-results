import Submission.SuccessorVaughanReduction

/-! Exact-type and permitted-axiom checks for the finite successor reduction. -/

open Nat Finset ArithmeticFunction
open scoped BigOperators ArithmeticFunction.zeta ArithmeticFunction.Moebius
open Erdos821.AnalyticSieve
open Erdos821.AnalyticSieve.SuccessorVaughan

example (w : ℕ → ℝ) (U V X : ℕ) :
    weightedSum vonMangoldt w X =
      weightedSum (shortPart vonMangoldt U) w X +
      hyperbolicSum (shortPart (μ : ArithmeticFunction ℝ) V) log w X -
      hyperbolicSum (vaughanTypeI U V) (ζ : ArithmeticFunction ℝ) w X +
      hyperbolicSum (vaughanTypeII V) (longPart vonMangoldt U) w X :=
  weighted_vaughan_identity w U V X

example (w : ℕ → ℝ) (X : ℕ) (hX : 1 ≤ X) (B : ℝ) (hB0 : 0 ≤ B)
    (hw : ∀ n ∈ Icc 1 X, 0 ≤ w n) (hB : ∀ n ∈ Icc 1 X, w n ≤ B) :
    weightedSum vonMangoldt w X ≤
      B*Real.log X*((positivePrimeOutputs w X).card : ℝ) +
      2*B*Real.sqrt X*Real.log X :=
  weighted_mangoldt_le_prime_outputs w X hX B hB0 hw hB

example (P A B : Finset ℕ) (n : ℕ) (hn : 2 ≤ n) :
    rectangleOutputWeight P A B n ≤ ((n-1).divisors.card : ℝ)^2 :=
  rectangleOutputWeight_le_divisors_sq P A B n hn

#print axioms weighted_vaughan_identity
#print axioms weighted_mangoldt_discrepancy_le
#print axioms weighted_prime_sum_le
#print axioms weighted_nonprime_sum_le
#print axioms weighted_mangoldt_le_prime_outputs
#print axioms prime_output_card_gt_of_vaughan_lower
#print axioms rectangle_weightedSum_eq
#print axioms rectangleOutputWeight_le_divisors_sq
#print axioms rectangleOutputWeight_one
#print axioms rectangle_typeII_eq
