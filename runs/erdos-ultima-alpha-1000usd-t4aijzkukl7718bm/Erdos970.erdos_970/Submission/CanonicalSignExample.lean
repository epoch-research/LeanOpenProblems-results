import Submission.FirstHitBooleanCost

/-! Canonical divisor-cutoff squares do not always have alternating Boolean
coefficient signs. The example is finite, exact, and uses distinct prime marginals.
It is not a new sieve bound. -/
namespace Erdos970.FiniteSelberg.CanonicalSignExample
open Finset
abbrev Pattern := Finset (Fin 5)

def prime : Fin 5 → ℕ := ![101, 103, 107, 109, 113]
def support : Finset Pattern := univ.filter (fun T => T.card ≤ 3)
def w (T : Pattern) : ℚ := ∏ i ∈ T, (1 / ((prime i : ℚ) - 1))
def G : ℚ := ∑ T ∈ support, w T
def c (T : Pattern) : ℚ := w T * if T ∈ support then 1 / G else 0
def ordinary (T : Pattern) : ℚ :=
  (-1)^T.card * (∏ i ∈ T, (prime i : ℚ)) * ∑ Q : Pattern, if T ⊆ Q then c Q else 0

def squareCoefficient (T : Pattern) : ℚ :=
  ∑ Q : Pattern, ∑ R : Pattern, if Q ∪ R = T then ordinary Q * ordinary R else 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem exact_example :
    (∀ i, (prime i).Prime) ∧ Function.Injective prime ∧
    (∀ T : Pattern, T.card ≤ 3 ↔ ∏ i ∈ T, prime i ≤ 113^3) ∧
    G = 3427577707/3269548800 ∧
    squareCoefficient univ = 108877434644698353576/11748288937523377849 ∧
    0 < squareCoefficient univ := by
  decide +kernel

noncomputable def marginal (i : Fin 5) : ℝ := 1 / (prime i : ℝ)

lemma support_eq_divisorSupport : support = divisorSupport prime (113^3) := by
  ext T
  simp only [support, mem_filter, mem_univ, true_and, mem_divisorSupport]
  exact exact_example.2.2.1 T

lemma weight_eq_cast (T : Pattern) : weight marginal T = (w T : ℝ) := by
  simp only [weight, w, Rat.cast_prod, Rat.cast_div, Rat.cast_one,
    Rat.cast_sub, Rat.cast_natCast]
  apply prod_congr rfl
  intro i hi
  have hp : (prime i : ℝ) ≠ 0 := by exact_mod_cast (exact_example.1 i).ne_zero
  dsimp [marginal]
  field_simp

lemma normalizer_eq_cast : normalizer marginal support = (G : ℝ) := by
  simp only [normalizer, G, Rat.cast_sum, weight_eq_cast, ← weight_eq_inverse_variance]

lemma canonical_eq_cast (T : Pattern) : canonicalOrthogonal marginal support T = (c T : ℝ) := by
  simp only [canonicalOrthogonal, c, weight_eq_cast, normalizer_eq_cast,
    Rat.cast_mul, apply_ite (fun x : ℚ => (x : ℝ)), Rat.cast_div, Rat.cast_one,
    Rat.cast_zero]

lemma ordinary_eq_cast (T : Pattern) :
    ordinaryCoefficient marginal (canonicalOrthogonal marginal support) T =
      (ordinary T : ℝ) := by
  simp only [ordinaryCoefficient, ordinary, canonical_eq_cast, Rat.cast_mul,
    Rat.cast_pow, Rat.cast_neg, Rat.cast_one, Rat.cast_prod, Rat.cast_natCast,
    Rat.cast_sum, apply_ite (fun x : ℚ => (x : ℝ)), Rat.cast_zero,
    marginal, div_eq_mul_inv, one_mul, prod_inv_distrib, inv_inv]

lemma squareCoefficient_eq_cast (T : Pattern) :
    booleanSquareCoefficient (ordinaryCoefficient marginal
      (canonicalOrthogonal marginal support)) T = (squareCoefficient T : ℝ) := by
  simp only [booleanSquareCoefficient, squareCoefficient, ordinary_eq_cast,
    Rat.cast_sum, apply_ite (fun x : ℚ => (x : ℝ)), Rat.cast_mul, Rat.cast_zero]

/-- The full coefficient is positive although the full pattern has odd cardinality. -/
theorem canonical_divisor_coefficient_positive :
    0 < booleanSquareCoefficient (ordinaryCoefficient marginal
      (canonicalOrthogonal marginal (divisorSupport prime (113^3)))) univ := by
  rw [← support_eq_divisorSupport, squareCoefficient_eq_cast]
  exact_mod_cast exact_example.2.2.2.2.2

theorem canonical_not_alternating :
    ¬ ∀ T : Pattern, 0 ≤ (-1 : ℝ)^T.card *
      booleanSquareCoefficient (ordinaryCoefficient marginal
        (canonicalOrthogonal marginal (divisorSupport prime (113^3)))) T := by
  intro h
  have hh := h univ
  have hc : (univ : Pattern).card = 5 := by decide
  rw [hc, show (-1 : ℝ)^5 = -1 by norm_num, neg_one_mul] at hh
  linarith [canonical_divisor_coefficient_positive]

#print axioms exact_example
#print axioms canonical_divisor_coefficient_positive
#print axioms canonical_not_alternating
end Erdos970.FiniteSelberg.CanonicalSignExample
