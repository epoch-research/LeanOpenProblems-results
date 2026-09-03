import Submission.FreshAttack

/-!
# Arithmetic certificates for factorial-gap integral constructions

This file does not import `Submission.Spec` and does not assert irrationality.
It verifies the integer-coefficient factorial-difference identity and the
endpoint Bezout identity used in the accompanying integral investigation.
The summability hypothesis in `integer_linear_form` is explicit for arbitrary
sequences. `newton_integer_linear_form` discharges it for every finite integer
Newton coefficient vector and every positive `k`.
-/

namespace FactorialIntegralCertificates

open FreshFactorialAttack

/-- The indexing is `p n = p_math (n+1)`. -/
noncomputable def scaled (p : ℕ → ℤ) (k n : ℕ) : ℝ :=
  (p n : ℝ) / ((n + 1).factorial : ℝ) ^ k

/-- A concrete sufficient hypothesis for the summability required below.
Polynomial sequences satisfy such an exponential bound. -/
lemma scaled_summable_of_exp_bound (p : ℕ → ℤ) (k : ℕ) (hk : 0 < k)
    (C R : ℝ) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hp : ∀ n, |(p n : ℝ)| ≤ C * R ^ n) : Summable (scaled p k) := by
  apply ((Real.summable_pow_div_factorial R).mul_left C).of_norm_bounded
  intro n
  have hf : (0 : ℝ) < (n + 1).factorial := by positivity
  have hf1 : (1 : ℝ) ≤ (n + 1).factorial := by
    exact_mod_cast Nat.factorial_pos (n + 1)
  have hpow : ((n + 1).factorial : ℝ) ≤ ((n + 1).factorial : ℝ) ^ k := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    have h1 : (1 : ℝ) ≤ ((n + 1).factorial : ℝ) ^ j := one_le_pow₀ hf1
    rw [pow_succ]
    nlinarith
  have hden : (n.factorial : ℝ) ≤ ((n + 1).factorial : ℝ) ^ k := by
    have hfac : (n.factorial : ℝ) ≤ (n + 1).factorial := by
      exact_mod_cast Nat.factorial_le (show n ≤ n + 1 by omega)
    exact hfac.trans hpow
  calc
    ‖scaled p k n‖ = |(p n : ℝ)| / ((n + 1).factorial : ℝ) ^ k := by
      simp [scaled, Real.norm_eq_abs]
    _ ≤ (C * R ^ n) / ((n + 1).factorial : ℝ) ^ k :=
      div_le_div_of_nonneg_right (hp n) (by positivity)
    _ ≤ (C * R ^ n) / (n.factorial : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = C * (R ^ n / (n.factorial : ℝ)) := by ring

/-- Integer-valued polynomials in the Newton/binomial basis. -/
def newtonSeq (c : ℕ → ℤ) (d n : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (d + 1), c j * (n.choose j : ℤ)

lemma newton_exp_bound (c : ℕ → ℤ) (d n : ℕ) :
    |(newtonSeq c d n : ℝ)| ≤
      (∑ j ∈ Finset.range (d + 1), |(c j : ℝ)|) * 2 ^ n := by
  unfold newtonSeq
  push_cast
  calc
    |∑ j ∈ Finset.range (d + 1), (c j : ℝ) * (n.choose j : ℝ)| ≤
        ∑ j ∈ Finset.range (d + 1), |(c j : ℝ) * (n.choose j : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range (d + 1), |(c j : ℝ)| * 2 ^ n := by
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (n.choose j : ℝ) from Nat.cast_nonneg _)]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact_mod_cast Nat.choose_le_two_pow n j
    _ = _ := (Finset.sum_mul _ _ _).symm

lemma scaled_newton_summable (c : ℕ → ℤ) (d k : ℕ) (hk : 0 < k) :
    Summable (scaled (newtonSeq c d) k) := by
  exact scaled_summable_of_exp_bound (newtonSeq c d) k hk
    (∑ j ∈ Finset.range (d + 1), |(c j : ℝ)|) 2
    (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (by norm_num)
    (newton_exp_bound c d)

lemma newton_zero (c : ℕ → ℤ) (d : ℕ) : newtonSeq c d 0 = c 0 := by
  unfold newtonSeq
  rw [Finset.sum_eq_single 0]
  · simp
  · intro j hj hj0
    rw [Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hj0)]
    simp
  · intro h0
    exact False.elim (h0 (by simp))




def correctionNumerator (p : ℕ → ℤ) (k n : ℕ) : ℤ :=
  (n + 2 : ℤ) ^ k * p n - p (n + 1)

noncomputable def correction (p : ℕ → ℤ) (k n : ℕ) : ℝ :=
  (correctionNumerator p k n : ℝ) / ((n + 2).factorial : ℝ) ^ k

noncomputable def residual (A : ℤ) (p : ℕ → ℤ) (k n : ℕ) : ℝ :=
  (A : ℝ) * term n + correction p k n

lemma correction_eq_difference (p : ℕ → ℤ) (k n : ℕ) :
    correction p k n = scaled p k n - scaled p k (n + 1) := by
  have hf : ((n + 1).factorial : ℝ) ≠ 0 := by positivity
  have hn : (n + 2 : ℝ) ≠ 0 := by positivity
  unfold correction correctionNumerator scaled
  push_cast
  rw [show n + 2 = (n + 1) + 1 by omega, Nat.factorial_succ]
  push_cast
  rw [mul_pow]
  field_simp
  ring

lemma finite_integer_linear_form (A : ℤ) (p : ℕ → ℤ) (k N : ℕ) :
    (∑ n ∈ Finset.range N, residual A p k n) =
      (A : ℝ) * partialSum N + (p 0 : ℝ) - scaled p k N := by
  simp_rw [residual, correction_eq_difference]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_range_sub']
  simp [partialSum, scaled]
  ring

lemma summable_residual (A : ℤ) (p : ℕ → ℤ) (k : ℕ)
    (hp : Summable (scaled p k)) : Summable (residual A p k) := by
  have ht : Summable (fun n => scaled p k (n + 1)) :=
    (summable_nat_add_iff 1).2 hp
  change Summable (fun n => residual A p k n)
  simp_rw [residual, correction_eq_difference]
  exact (summable_term.mul_left (A : ℝ)).add (hp.sub ht)

/-- Exact normalization: the two coefficients are the integers `A` and `p 0`.
No denominator of a finite prefix is cleared, and no auxiliary constant occurs. -/
lemma integer_linear_form (A : ℤ) (p : ℕ → ℤ) (k : ℕ)
    (hp : Summable (scaled p k)) :
    (∑' n, residual A p k n) = (A : ℝ) * series + (p 0 : ℝ) := by
  have ht : Summable (fun n => scaled p k (n + 1)) :=
    (summable_nat_add_iff 1).2 hp
  simp_rw [residual, correction_eq_difference]
  rw [Summable.tsum_add (summable_term.mul_left (A : ℝ)) (hp.sub ht),
    tsum_mul_left, hp.tsum_sub ht]
  have h := hp.tsum_eq_zero_add
  have h0 : scaled p k 0 = (p 0 : ℝ) := by simp [scaled]
  rw [h0] at h
  change (A : ℝ) * series + _ = _
  linarith

/-- The construction for any finite integer Newton coefficient vector,
with summability discharged rather than assumed. -/
lemma newton_integer_linear_form (A : ℤ) (c : ℕ → ℤ) (d k : ℕ) (hk : 0 < k) :
    (∑' n, residual A (newtonSeq c d) k n) = (A : ℝ) * series + (c 0 : ℝ) := by
  rw [integer_linear_form A (newtonSeq c d) k (scaled_newton_summable c d k hk),
    newton_zero]

/-- Positivity of the residuals and one explicit positive residual give a
nonzero *integer-coefficient* linear form, rather than only analytic decay. -/
lemma positive_integer_linear_form (A : ℤ) (p : ℕ → ℤ) (k : ℕ)
    (hp : Summable (scaled p k))
    (hnonneg : ∀ n, 0 ≤ residual A p k n)
    (n : ℕ) (hn : 0 < residual A p k n) :
    0 < (A : ℝ) * series + (p 0 : ℝ) := by
  rw [← integer_linear_form A p k hp]
  exact lt_of_lt_of_le hn ((summable_residual A p k hp).le_tsum n
    (fun j _ => hnonneg j))

/-- A smooth-coefficient Bezout identity for consecutive factorial-minus-one
numbers. Here the mathematical factorial index is `n+2`. -/
lemma endpoint_bezout (n : ℕ) :
    ((n + 1).factorial : ℤ) * ((n + 3).factorial - 1) -
      (((n + 3 : ℤ) * (n + 1).factorial + 1) * ((n + 2).factorial - 1)) = 1 := by
  have h2 : (n + 2).factorial = (n + 2) * (n + 1).factorial := by
    simpa [Nat.add_assoc] using Nat.factorial_succ (n + 1)
  have h3 : (n + 3).factorial = (n + 3) * (n + 2).factorial := by
    simpa [Nat.add_assoc] using Nat.factorial_succ (n + 2)
  rw [h3, h2]
  push_cast
  ring

lemma endpoint_reciprocal_identity (n : ℕ) :
    (1 : ℝ) / (((n + 2).factorial - 1) * ((n + 3).factorial - 1)) =
      ((n + 1).factorial : ℝ) / ((n + 2).factorial - 1) -
        (((n + 3 : ℝ) * (n + 1).factorial + 1) / ((n + 3).factorial - 1)) := by
  have h2 := denominator_ne_zero n
  have h3 : ((n + 3).factorial : ℝ) - 1 ≠ 0 := by
    simpa [Nat.add_assoc] using denominator_ne_zero (n + 1)
  have hz : ((n + 1).factorial : ℝ) * ((n + 3).factorial - 1) -
      (((n + 3 : ℝ) * (n + 1).factorial + 1) * ((n + 2).factorial - 1)) = 1 := by
    exact_mod_cast endpoint_bezout n
  field_simp
  nlinarith [hz]

/-- Integer numerator before division by `(F-1)*F^k`. -/
def numerator (A h F : ℤ) (k : ℕ) : ℤ :=
  A * F ^ k + (F - 1) * h

lemma numerator_mod (A h F : ℤ) (k : ℕ) :
    numerator A h F k ≡ A [ZMOD (F - 1)] := by
  have hF : F ≡ 1 [ZMOD (F - 1)] := by
    rw [Int.modEq_iff_dvd]
    use -1
    ring
  have hp : F ^ k ≡ 1 [ZMOD (F - 1)] := by
    simpa using hF.pow k
  have hh : (F - 1) * h ≡ 0 [ZMOD (F - 1)] := by
    rw [Int.modEq_iff_dvd]
    use -h
    ring
  simpa [numerator] using (Int.ModEq.refl A |>.mul hp).add hh

/-- This is the exact residue obstruction responsible for nonvanishing. -/
lemma numerator_nonzero (A h F : ℤ) (k : ℕ)
    (hA : 0 < A) (hAF : A < F - 1) : numerator A h F k ≠ 0 := by
  intro hz
  have hm := numerator_mod A h F k
  change numerator A h F k % (F - 1) = A % (F - 1) at hm
  rw [hz, Int.zero_emod, Int.emod_eq_of_lt hA.le hAF] at hm
  omega

lemma residual_eq_numerator (A : ℤ) (p : ℕ → ℤ) (k n : ℕ) :
    residual A p k n =
      (numerator A (correctionNumerator p k n) (n + 2).factorial k : ℝ) /
        ((((n + 2).factorial : ℝ) - 1) * ((n + 2).factorial : ℝ) ^ k) := by
  have ha := denominator_ne_zero n
  have hf : ((n + 2).factorial : ℝ) ≠ 0 := by positivity
  unfold residual correction term numerator
  push_cast
  field_simp

lemma residual_nonzero_of_bound (A : ℤ) (p : ℕ → ℤ) (k n : ℕ)
    (hA : 0 < A) (hn : A < ((n + 2).factorial : ℤ) - 1) :
    residual A p k n ≠ 0 := by
  rw [residual_eq_numerator]
  apply div_ne_zero
  · exact_mod_cast numerator_nonzero A (correctionNumerator p k n)
      (n + 2).factorial k hA hn
  · exact mul_ne_zero (denominator_ne_zero n) (pow_ne_zero _ (by positivity))

lemma positive_integer_linear_form_of_congruence
    (A : ℤ) (p : ℕ → ℤ) (k : ℕ)
    (hp : Summable (scaled p k)) (hA : 0 < A)
    (hnonneg : ∀ n, 0 ≤ residual A p k n)
    (n : ℕ) (hn : A < ((n + 2).factorial : ℤ) - 1) :
    0 < (A : ℝ) * series + (p 0 : ℝ) := by
  apply positive_integer_linear_form A p k hp hnonneg n
  exact lt_of_le_of_ne (hnonneg n) (Ne.symm (residual_nonzero_of_bound A p k n hA hn))

/-- Scaled version of the explicit quartic used in the exact verification.
It is an integer polynomial; its primitive linear form is `4*S-5`. -/
def exampleP (n : ℤ) : ℤ :=
  7995 * n ^ 4 - 81146 * n ^ 3 + 286605 * n ^ 2 - 411790 * n + 198216

def exampleH (n : ℤ) : ℤ := n ^ 3 * exampleP (n - 1) - exampleP n

lemma example_boundary : exampleP 1 = -120 := by decide

lemma example_small_values :
    exampleH 2 = -768 ∧ exampleH 3 = -4128 ∧
      exampleH 4 = -57696 ∧ exampleH 5 = -1394016 := by decide

lemma example_shifted_identity (u : ℤ) :
    exampleH (u + 6) =
      7995 * u ^ 7 + 222664 * u ^ 6 + 2549697 * u ^ 5 +
      15426137 * u ^ 4 + 52658546 * u ^ 3 + 99830511 * u ^ 2 +
      94909306 * u + 33252216 := by
  simp only [exampleH, exampleP]
  ring

lemma example_tail_positive (u : ℤ) (hu : 0 ≤ u) :
    0 < exampleH (u + 6) := by
  rw [example_shifted_identity]
  positivity

end FactorialIntegralCertificates
