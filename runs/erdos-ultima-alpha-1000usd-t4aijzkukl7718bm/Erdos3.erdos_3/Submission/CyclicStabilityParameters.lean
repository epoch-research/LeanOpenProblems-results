import Submission.NearMaximalCyclicInverse

/-! Explicit power-law tolerances for the cyclic near-maximal inverse theorem.
These are quantitative stability parameters, not a small-uniformity inverse. -/
namespace Erdos3CyclicStabilityParameters
open Erdos3HigherPolynomialSeparation
set_option maxHeartbeats 2000000

def stabilityExponent : ℕ → ℕ
  | 0 => 2
  | n+1 => 2+2*stabilityExponent n

def stabilityCost : ℕ → ℕ
  | 0 => 1
  | n+1 => 4+stabilityCost n+(2*n+5)*stabilityExponent n

noncomputable def phaseTolerance (n : ℕ) (ε : ℝ) : ℝ :=
  (1/2)^stabilityCost n*ε^stabilityExponent n

noncomputable def derivativeAccuracy (n : ℕ) (ε : ℝ) : ℝ := polynomialGap n*ε^2/32

lemma stabilityExponent_identity (n : ℕ) : stabilityExponent n+2 = 2^(n+2) := by
  induction n with
  | zero => norm_num [stabilityExponent]
  | succ n ih =>
    rw [stabilityExponent,pow_succ 2 (n+2)]
    omega

lemma stabilityExponent_pos (n : ℕ) : 0 < stabilityExponent n := by
  cases n <;> simp only [stabilityExponent] <;> omega

lemma phaseTolerance_pos (n : ℕ) {ε : ℝ} (hε : 0 < ε) : 0 < phaseTolerance n ε :=
  mul_pos (pow_pos (by norm_num) _) (pow_pos hε _)

lemma phaseTolerance_zero (ε : ℝ) : phaseTolerance 0 ε = ε^2/2 := by
  unfold phaseTolerance stabilityCost stabilityExponent
  ring

lemma gap_dyadic (n : ℕ) : polynomialGap n/32 = (1/2 : ℝ)^(2*n+5) := by
  unfold polynomialGap
  rw [pow_add,pow_mul]
  norm_num only [show (1/2 : ℝ)^2 = 1/4 by norm_num,show (1/2 : ℝ)^5 = 1/32 by norm_num]
  ring

lemma derivativeAccuracy_dyadic (n : ℕ) (ε : ℝ) :
    derivativeAccuracy n ε = (1/2 : ℝ)^(2*n+5)*ε^2 := by
  rw [← gap_dyadic]
  unfold derivativeAccuracy
  ring

lemma phaseTolerance_succ (n : ℕ) (ε : ℝ) :
    phaseTolerance (n+1) ε = (ε^2/16)*phaseTolerance n (derivativeAccuracy n ε) := by
  rw [derivativeAccuracy_dyadic]
  unfold phaseTolerance
  rw [stabilityCost,stabilityExponent]
  rw [pow_add (1/2 : ℝ) (4+stabilityCost n) ((2*n+5)*stabilityExponent n),
    pow_add (1/2 : ℝ) 4 (stabilityCost n),pow_mul (1/2 : ℝ) (2*n+5) (stabilityExponent n),
    pow_add ε 2 (2*stabilityExponent n),pow_mul ε 2 (stabilityExponent n),mul_pow]
  norm_num only [show (1/2 : ℝ)^4 = 1/16 by norm_num]
  ring

lemma derivativeAccuracy_pos (n : ℕ) {ε : ℝ} (hε : 0 < ε) : 0 < derivativeAccuracy n ε :=
  div_pos (mul_pos (polynomialGap_pos n) (sq_pos_of_pos hε)) (by norm_num)

lemma stability_parameter_bounds (n : ℕ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    derivativeAccuracy n ε ≤ 1 ∧ 3*derivativeAccuracy n ε < polynomialGap n/2 ∧
    ε^2/16 ≤ 1/8 ∧ 4*derivativeAccuracy n ε+2*(ε^2/16) ≤ ε^2 := by
  have he2 : ε^2 ≤ 1 := by nlinarith only [hε,hε1]
  have hg := polynomialGap_pos n
  have hg1 := polynomialGap_le_one n
  have hηg : derivativeAccuracy n ε ≤ polynomialGap n/32 :=
    div_le_div_of_nonneg_right (mul_le_of_le_one_right hg.le he2) (by norm_num)
  have hηe : derivativeAccuracy n ε ≤ ε^2/32 :=
    div_le_div_of_nonneg_right (mul_le_of_le_one_left (sq_nonneg ε) hg1) (by norm_num)
  refine ⟨?_,?_,?_,?_⟩ <;> linarith only [hηg,hηe,hg,hg1,he2,sq_nonneg ε]

lemma phaseTolerance_le (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) : phaseTolerance n ε ≤ ε := by
  have hc : (1/2 : ℝ)^stabilityCost n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have he : ε^stabilityExponent n ≤ ε := by
    simpa only [pow_one] using pow_le_pow_of_le_one hε hε1 (stabilityExponent_pos n)
  exact (mul_le_mul_of_nonneg_right hc (pow_nonneg hε _)).trans (by simpa only [one_mul] using he)

#print axioms phaseTolerance_succ
#print axioms stability_parameter_bounds
end Erdos3CyclicStabilityParameters
