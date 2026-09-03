import Submission.DyadicThreeAPBound

/-! The explicit dyadic group bound has a polynomial exponent. -/
namespace Erdos3PolynomialThreeAPThreshold
open Finset Erdos3DyadicThreeAPBound Erdos3FiniteThreeAPBound Erdos3LocalDensityStep
  Erdos3LocalThreeAPIncrement Erdos3RelativeStableBohr Erdos3StableSupportedIncrement
  Erdos3BohrIncrementParameters
open scoped BigOperators Classical Polynomial
set_option maxHeartbeats 3500000

def scaleExponent (b k m : ℕ) : ℕ := 3*k+2*m+3*rankBudget m+35*b+50
def thresholdExponent (l : ℕ) : ℕ :=
  let m := supportParameter l
  let b := finalRank l
  let k := m+20
  let t := iterationSteps l
  5+2*l+2*b*(k+7*b+8)+2*b*(3+scaleExponent b k m*t)

lemma mul_pow_two_bound {a b i j : ℕ} (ha : a ≤ 2^i) (hb : b ≤ 2^j) : a*b ≤ 2^(i+j) := by
  rw [pow_add]
  exact Nat.mul_le_mul ha hb
lemma pow_pow_two_bound {a i : ℕ} (ha : a ≤ 2^i) (n : ℕ) : a^n ≤ 2^(i*n) := by
  rw [pow_mul]
  exact Nat.pow_le_pow_left ha n

lemma windowDenominator_pow_bound (d k : ℕ) : windowDenominator d (2^k) ≤ 2^(k+7*d+3) := by
  have h : 7*d+1 ≤ 2^(7*d+1) := (7*d+1).lt_two_pow_self.le
  calc
    _ = 2^(k+2)*(7*d+1) := by unfold windowDenominator; rw [pow_add]; norm_num; ring
    _ ≤ 2^((k+2)+(7*d+1)) := mul_pow_two_bound le_rfl h
    _ = _ := by congr 1; omega

lemma stabilityDenominator_eq (m : ℕ) :
    stabilityDenominator m (rankBudget m) = 2^(m+2*rankBudget m+12) := by
  unfold stabilityDenominator
  rw [show 1024 = (2 : ℕ)^10 by decide, show 4 = (2 : ℕ)^2 by decide, ← pow_mul,
    ← pow_add, ← pow_add]
  congr 1
  omega

lemma localShrink_pow_bound (b k m : ℕ) :
    localShrinkDenominator b (2^k) m ≤ 2^(k+m+2*rankBudget m+21*b+25) := by
  have h₁ := windowDenominator_pow_bound b k
  have h₂ : windowDenominator b 1 ≤ 2^(7*b+3) := by simpa using windowDenominator_pow_bound b 0
  have h₃ : windowDenominator b (stabilityDenominator m (rankBudget m)) ≤
      2^((m+2*rankBudget m+12)+7*b+3) := by
    rw [stabilityDenominator_eq]
    exact windowDenominator_pow_bound _ _
  have hh := mul_pow_two_bound (mul_pow_two_bound (mul_pow_two_bound
    (by decide : 16 ≤ (2 : ℕ)^4) h₁) h₂) h₃
  rw [show (4+(k+7*b+3)+(7*b+3))+((m+2*rankBudget m+12)+7*b+3) =
    k+m+2*rankBudget m+21*b+25 by omega] at hh
  exact hh

lemma stepShrink_pow_bound (b k m : ℕ) :
    stepShrinkDenominator b (2^k) m ≤ 2^(3*k+m+2*rankBudget m+35*b+37) := by
  have hh := mul_pow_two_bound (mul_pow_two_bound (by decide : 64 ≤ (2 : ℕ)^6)
    (pow_pow_two_bound (windowDenominator_pow_bound b k) 2)) (localShrink_pow_bound b k m)
  rw [show (6+(k+7*b+3)*2)+(k+m+2*rankBudget m+21*b+25) =
    3*k+m+2*rankBudget m+35*b+37 by omega] at hh
  exact hh

lemma generatorDenominator_pow_bound (m : ℕ) : generatorDenominator m ≤ 2^(m+rankBudget m+12) := by
  have hh := mul_pow_two_bound (mul_pow_two_bound (by decide : 2048 ≤ (2 : ℕ)^11)
    ((rankBudget m+1).lt_two_pow_self.le)) (le_refl (2^m))
  rw [show (11+(rankBudget m+1))+m = m+rankBudget m+12 by omega] at hh
  exact hh

lemma iterationScale_pow_bound (b k m : ℕ) : iterationScale b (2^k) m ≤ 2^(scaleExponent b k m) := by
  have hh := mul_pow_two_bound (mul_pow_two_bound (by decide : 2 ≤ (2 : ℕ)^1)
    (stepShrink_pow_bound b k m)) (generatorDenominator_pow_bound m)
  rw [show (1+(3*k+m+2*rankBudget m+35*b+37))+(m+rankBudget m+12) =
    scaleExponent b k m by unfold scaleExponent; omega] at hh
  exact hh

lemma coverFactor_pow_bound (b k : ℕ) : coverFactor b (2^k) ≤ 2^(2*b*(k+7*b+8)) := by
  have hp := windowDenominator_pos b (pow_pos (by decide : 0 < (2 : ℕ)) k)
  have hb : 16*windowDenominator b (2^k)+1 ≤ 32*windowDenominator b (2^k) := by omega
  have hh := hb.trans (mul_pow_two_bound (by decide : 32 ≤ (2 : ℕ)^5) (windowDenominator_pow_bound b k))
  have he := pow_pow_two_bound hh (2*b)
  rw [show (5+(k+7*b+3))*(2*b) = 2*b*(k+7*b+8) by ring] at he
  exact he

lemma iterationVolume_pow_bound (b k m t : ℕ) :
    iterationVolume b (2^k) m t ≤ 2^(2*b*(3+scaleExponent b k m*t)) := by
  have hp : 0 < (iterationScale b (2^k) m)^t :=
    pow_pos (iterationScale_pos b m (pow_pos (by decide) k)) t
  have hb : 4*(iterationScale b (2^k) m)^t+1 ≤ 8*(iterationScale b (2^k) m)^t := by omega
  have hh := hb.trans (mul_pow_two_bound (by decide : 8 ≤ (2 : ℕ)^3)
    (pow_pow_two_bound (iterationScale_pow_bound b k m) t))
  have he := pow_pow_two_bound hh (2*b)
  rw [mul_comm (3+scaleExponent b k m*t) (2*b)] at he
  exact he

/-- The threshold exponent is built only from additions, multiplications and fixed powers of l. -/
theorem dyadicGroupBound_le_pow_threshold (l : ℕ) : dyadicGroupBound l ≤ 2^(thresholdExponent l) := by
  have hh := mul_pow_two_bound (mul_pow_two_bound (mul_pow_two_bound
    (by decide : 32 ≤ (2 : ℕ)^5) (le_refl (2^(2*l))))
    (coverFactor_pow_bound (finalRank l) (supportParameter l+20)))
    (iterationVolume_pow_bound (finalRank l) (supportParameter l+20) (supportParameter l) (iterationSteps l))
  exact hh

noncomputable def momentPolynomial : Polynomial ℝ := 2*(Polynomial.X+40)
noncomputable def supportPolynomial : Polynomial ℝ := 8*momentPolynomial*(Polynomial.X+1)+1
noncomputable def samplePolynomial : Polynomial ℝ :=
  256*supportPolynomial^4*(1024*(supportPolynomial+10))^2
noncomputable def rankPolynomial : Polynomial ℝ := 32*(1+supportPolynomial*samplePolynomial)
noncomputable def iterationsPolynomial : Polynomial ℝ := 1024*(Polynomial.X+1)
noncomputable def finalRankPolynomial : Polynomial ℝ := iterationsPolynomial*rankPolynomial
noncomputable def scalePolynomial : Polynomial ℝ :=
  3*(supportPolynomial+20)+2*supportPolynomial+3*rankPolynomial+35*finalRankPolynomial+50
noncomputable def thresholdPolynomial : Polynomial ℝ :=
  5+2*Polynomial.X+2*finalRankPolynomial*(supportPolynomial+20+7*finalRankPolynomial+8)+
    2*finalRankPolynomial*(3+scalePolynomial*iterationsPolynomial)

lemma eval_thresholdPolynomial (l : ℕ) :
    thresholdPolynomial.eval (l : ℝ) = (thresholdExponent l : ℝ) := by
  simp only [thresholdPolynomial, scalePolynomial, finalRankPolynomial, iterationsPolynomial,
    rankPolynomial, samplePolynomial, supportPolynomial, momentPolynomial,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat, Polynomial.eval_X, Polynomial.eval_one,
    thresholdExponent, scaleExponent, finalRank, iterationSteps, rankBudget, sampleCount,
    sampleAccuracy, walkSteps, supportParameter, momentParameter, Nat.cast_add, Nat.cast_mul,
    Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]

lemma polynomial_geometric_summable (P : Polynomial ℝ) :
    Summable (fun n : ℕ ↦ P.eval (n : ℝ)*(1/2 : ℝ)^n) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    simpa only [Polynomial.eval_add, add_mul] using hP.add hQ
  | monomial k c =>
    have h := (summable_pow_mul_geometric_of_norm_lt_one k (by norm_num : ‖(1/2 : ℝ)‖ < 1)).mul_left c
    simpa only [Polynomial.eval_monomial, mul_assoc] using h

/-- The density-level thresholds have summable geometric weight. -/
theorem summable_threshold_weight : Summable (fun l : ℕ ↦ (thresholdExponent l : ℝ)*(1/2 : ℝ)^l) := by
  simpa only [eval_thresholdPolynomial] using polynomial_geometric_summable thresholdPolynomial

variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem threeAPFree_card_lt_pow_threshold (h2 : Function.Bijective (fun x : G ↦ x+x))
    (A : Finset G) (hA : A.Nonempty) (hfree : ThreeAPFree (A : Set G))
    (l : ℕ) (hdensity : dyadicDensity l ≤ Erdos3CorrelationSifting.density A) :
    Fintype.card G < 2^(thresholdExponent l) :=
  (threeAPFree_card_lt_dyadic_bound h2 A hA hfree l hdensity).trans_le (dyadicGroupBound_le_pow_threshold l)

#print axioms dyadicGroupBound_le_pow_threshold
#print axioms summable_threshold_weight
#print axioms threeAPFree_card_lt_pow_threshold
end Erdos3PolynomialThreeAPThreshold
