import Submission.SuccessorTypeIIGram

/-! Expanded-kernel and permitted-axiom audits for the successor Gram reduction. -/
open Nat Finset ArithmeticFunction
open scoped BigOperators
open Erdos821.AnalyticSieve
open Erdos821.AnalyticSieve.SuccessorVaughan

example {ι κ : Type*} (A : Finset ι) (B : Finset κ)
    (a : ι → ℝ) (b : κ → ℝ) (K : ι → κ → ℝ) :
    (∑ r ∈ A, ∑ s ∈ B, a r*b s*K r s)^4 ≤
      (∑ r ∈ A, (a r)^2)^2*(∑ s ∈ B, (b s)^2)^2*
        (∑ r ∈ A, ∑ t ∈ A, (∑ s ∈ B, K r s*K t s)^2) :=
  kernelBilinear_fourth_le A B a b K

example (w v : ℕ → ℝ) (N U V : ℕ) (hV : 1 ≤ V) :
    (∑ r ∈ Icc 1 N, ∑ s ∈ Icc 1 N, if r*s ≤ N then
      (vaughanTypeII V r*longPart vonMangoldt U s)*(w (r*s)-v (r*s)) else 0)^4 ≤
    ((typeIILevels N U V).card : ℝ)^3*
      ∑ j ∈ typeIILevels N U V, successorTypeIIBlockFourthMajorant w v N U V j :=
  successor_typeII_fourth_le_gram_sum w v N U V hV

example (w v : ℕ → ℝ) (N U V : ℕ) (hN : 1 ≤ N) (hV : 1 ≤ V)
    (B K E : ℝ) (hB0 : 0 ≤ B) (hE : 0 ≤ E)
    (hw : ∀ n ∈ Icc 1 N, 0 ≤ w n) (hB : ∀ n ∈ Icc 1 N, w n ≤ B)
    (Hgram : ((typeIILevels N U V).card : ℝ)^3*
      (∑ j ∈ typeIILevels N U V, successorTypeIIBlockFourthMajorant w v N U V j) ≤ E^4)
    (Hmain : B*Real.log N*K+2*B*Real.sqrt N*Real.log N+
      successorTypeIError w v N U V+E < ∑ n ∈ Icc 1 N, vonMangoldt n*v n) :
    K < (((Icc 1 N).filter (fun n => n.Prime ∧ 0 < w n)).card : ℝ) :=
  prime_output_card_gt_of_gram w v N U V hN hV B K E hB0 hE hw hB Hgram Hmain

#print axioms kernelGramEnergy_nonneg
#print axioms column_projection_square
#print axioms kernelBilinear_fourth_le
#print axioms rowGram_self_nonneg
#print axioms rowGram_self_le
#print axioms kernelGramEnergy_le_of_correlations
#print axioms hyperbolic_discrepancy_eq_kernelBilinear
#print axioms successor_typeII_block_fourth_le
#print axioms kernelGramEnergy_four_corners
#print axioms sum_fourth_le_card_cube
#print axioms successor_typeII_dyadic
#print axioms successor_typeII_fourth_le_gram_sum
#print axioms successor_typeII_abs_le_of_gram
#print axioms prime_output_card_gt_of_gram
#print axioms rectangle_positive_output_smooth
