import Submission.SelbergEnergyCriterion

/-! An exact finite example showing that signed orthogonal coefficients can improve
the mean-plus-L1-cost objective over the positive cutoff profile. This is not a
Jacobsthal bound or an asymptotic optimization theorem. -/
namespace Erdos970.SelbergSignedExample
open Finset
abbrev Pattern := Finset (Fin 6)

def prime : Fin 6 → ℕ := ![2, 3, 5, 7, 11, 13]
def variance (Q : Pattern) : ℚ := ∏ i ∈ Q, ((prime i - 1 : ℕ) : ℚ)
def height (Q : Pattern) : ℕ := ∏ i ∈ Q, (prime i + 1)
def primeProduct (Q : Pattern) : ℚ := ∏ i ∈ Q, (prime i : ℚ)
def base (Q : Pattern) : ℚ := ((24192 - height Q : ℕ) : ℚ) / variance Q
def signed (Q : Pattern) : ℚ := base Q - (1000 / 30030) * (-1) ^ Q.card

def ordinary (c : Pattern → ℚ) (T : Pattern) : ℚ :=
  (-1) ^ T.card * primeProduct T * ∑ Q : Pattern, if T ⊆ Q then c Q else 0

def cost (c : Pattern → ℚ) : ℚ := ∑ T : Pattern, |ordinary c T|
def meanSquare (c : Pattern → ℚ) : ℚ := ∑ Q : Pattern, c Q ^ 2 * variance Q
def objective (c : Pattern → ℚ) : ℚ := (32668496 / 5) * meanSquare c + cost c ^ 2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem exact_example :
    (∀ Q : Pattern, 0 ≤ base Q) ∧
    (∑ Q : Pattern, signed Q) = (∑ Q : Pattern, base Q) ∧
    signed univ < 0 ∧
    (∀ T : Pattern, ordinary signed T = ordinary base T - if T = univ then 1000 else 0) ∧
    cost base = 32668496 / 5 ∧
    cost signed = cost base + 1000 ∧
    objective signed < objective base := by
  decide +kernel

noncomputable def marginal (i : Fin 6) : ℝ := 1 / (prime i : ℝ)

lemma prime_isPrime (i : Fin 6) : (prime i).Prime := by
  have h : ∀ i : Fin 6, (prime i).Prime := by decide +kernel
  exact h i

lemma marginal_bounds (i : Fin 6) : 0 < marginal i ∧ marginal i < 1 := by
  have hp : (1 : ℝ) < prime i := by exact_mod_cast (prime_isPrime i).one_lt
  dsimp [marginal]
  exact ⟨by positivity, (div_lt_one (by linarith)).mpr hp⟩

lemma real_variance (Q : Pattern) : FiniteSelberg.variance marginal Q = (variance Q : ℝ) := by
  simp only [FiniteSelberg.variance, variance, Rat.cast_prod]
  apply prod_congr rfl
  intro i hi
  have hp0 : (prime i : ℝ) ≠ 0 := by exact_mod_cast (prime_isPrime i).ne_zero
  rw [Rat.cast_natCast, Nat.cast_sub (prime_isPrime i).one_le, Nat.cast_one]
  dsimp [marginal]
  field_simp

lemma real_ordinary (c : Pattern → ℚ) (T : Pattern) :
    FiniteSelberg.ordinaryCoefficient marginal (fun Q => (c Q : ℝ)) T = (ordinary c T : ℝ) := by
  simp only [FiniteSelberg.ordinaryCoefficient, ordinary, Rat.cast_mul, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_one, Rat.cast_sum, apply_ite (fun x : ℚ => (x : ℝ)), Rat.cast_zero,
    primeProduct, Rat.cast_prod, Rat.cast_natCast, marginal, div_eq_mul_inv, one_mul, prod_inv_distrib, inv_inv]

lemma real_cost (c : Pattern → ℚ) :
    FiniteSelberg.kernelCost marginal (fun Q => (c Q : ℝ)) = (cost c : ℝ) := by
  simp only [FiniteSelberg.kernelCost, cost, Rat.cast_sum, Rat.cast_abs, real_ordinary]

lemma real_meanSquare (c : Pattern → ℚ) :
    FiniteSelberg.average marginal (fun ω =>
      FiniteSelberg.linearKernel marginal (fun Q => (c Q : ℝ)) ω ^ 2) = (meanSquare c : ℝ) := by
  rw [show (fun ω => FiniteSelberg.linearKernel marginal (fun Q => (c Q : ℝ)) ω ^ 2) =
      (fun ω => (∑ Q : Pattern, (c Q : ℝ) * FiniteSelberg.basis marginal Q ω) ^ 2) by rfl,
    FiniteSelberg.average_square_sum marginal (fun i => (marginal_bounds i).1.ne')]
  simp only [meanSquare, Rat.cast_sum, Rat.cast_mul, Rat.cast_pow, real_variance]

/-- The exact rational comparison concerns the actual real mean and coefficient cost
used by the interval sieve, not an unrelated surrogate function. -/
theorem real_objective_improves :
    (32668496 / 5 : ℝ) * FiniteSelberg.average marginal (fun ω =>
      FiniteSelberg.linearKernel marginal (fun Q => (signed Q : ℝ)) ω ^ 2) +
      FiniteSelberg.kernelCost marginal (fun Q => (signed Q : ℝ)) ^ 2 <
    (32668496 / 5 : ℝ) * FiniteSelberg.average marginal (fun ω =>
      FiniteSelberg.linearKernel marginal (fun Q => (base Q : ℝ)) ω ^ 2) +
      FiniteSelberg.kernelCost marginal (fun Q => (base Q : ℝ)) ^ 2 := by
  rw [real_meanSquare, real_meanSquare, real_cost, real_cost]
  have h := exact_example.2.2.2.2.2.2
  dsimp only [objective] at h
  have hh : ((32668496 / 5 * meanSquare signed + cost signed ^ 2 : ℚ) : ℝ) <
      ((32668496 / 5 * meanSquare base + cost base ^ 2 : ℚ) : ℝ) := Rat.cast_lt.mpr h
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_pow, Rat.cast_div, Rat.cast_ofNat] using hh

lemma base_sum_pos : (0 : ℚ) < ∑ Q : Pattern, base Q := by
  have hpos : (0 : ℚ) < base ∅ := by decide +kernel
  exact (sum_pos_iff_of_nonneg (fun Q _ => exact_example.1 Q)).mpr ⟨∅, mem_univ _, hpos⟩

noncomputable def normalizedSquare (c : Pattern → ℚ) (ω : Fin 6 → Bool) : ℝ :=
  (FiniteSelberg.linearKernel marginal (fun Q => (c Q : ℝ)) ω / (∑ Q : Pattern, (base Q : ℝ))) ^ 2

lemma normalizedSquare_upper (c : Pattern → ℚ)
    (hc : (∑ Q : Pattern, c Q) = ∑ Q : Pattern, base Q) (ω : Fin 6 → Bool) :
    (if ω = (fun _ => false) then (1 : ℝ) else 0) ≤ normalizedSquare c ω := by
  classical
  by_cases hω : ω = (fun _ => false)
  · subst ω
    have hsum : (∑ Q : Pattern, (c Q : ℝ)) = ∑ Q : Pattern, (base Q : ℝ) := by exact_mod_cast hc
    have hn : (∑ Q : Pattern, (base Q : ℝ)) ≠ 0 := ne_of_gt (by exact_mod_cast base_sum_pos)
    simp only [normalizedSquare, FiniteSelberg.linearKernel, FiniteSelberg.basis_at_empty,
      mul_one, hsum, div_self hn, one_pow, if_true, le_refl]
  · simp only [if_neg hω, normalizedSquare]
    exact sq_nonneg _

/-- Both the original and the improved signed kernel give valid normalized upper
weights on every Boolean hit pattern. -/
theorem both_upper (ω : Fin 6 → Bool) :
    (if ω = (fun _ => false) then (1 : ℝ) else 0) ≤ normalizedSquare base ω ∧
    (if ω = (fun _ => false) then (1 : ℝ) else 0) ≤ normalizedSquare signed ω :=
  ⟨normalizedSquare_upper base rfl ω, normalizedSquare_upper signed exact_example.2.1 ω⟩

#print axioms exact_example
#print axioms real_objective_improves
#print axioms both_upper
end Erdos970.SelbergSignedExample
