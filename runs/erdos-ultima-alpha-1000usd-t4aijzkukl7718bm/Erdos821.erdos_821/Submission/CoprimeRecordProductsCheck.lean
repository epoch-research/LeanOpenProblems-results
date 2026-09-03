import Submission.CoprimeRecordProducts

/-! Exact-type and axiom checks for coprime-pair product counting. -/

open Nat Filter
open Erdos821 Erdos821.CoprimeRecords

example (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ K : ℕ,
      ((coprimePairs K n).card : ℝ) ≤ (n : ℝ)^ε*(gAvoiding K (n^2) : ℝ) :=
  eventually_coprimePairs_card_le_mul_gAvoiding_square ε hε

example (γ : ℝ) (hγ : 1/2 < γ)
    (hupper : γ < 1/2 + 1/(80000000*Sieve.totientRatioAverageConstant+10)) :
    ∃ B : ℕ, {n : ℕ | 1 < n ∧
      (((n^2 : ℕ) : ℝ)^γ) < (gAvoiding B.factorial (n^2) : ℝ)}.Infinite :=
  infinite_square_output_multiplicity γ hγ hupper

#print axioms coprimePair_inputs_pos
#print axioms coprimePair_product_bound
#print axioms coprimePair_productImage_card_le
#print axioms coprimePairs_card_le_divisor_bound
#print axioms eventually_coprimePairs_card_le_mul_gAvoiding_square
#print axioms infinite_square_output_multiplicity
