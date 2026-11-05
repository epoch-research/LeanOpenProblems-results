import Submission.RamseyTools
import Submission.SmallRamsey

/-!
# Exact reduction and a conditional recurrence criterion for the fixed statement

The coefficient in the fixed statement is a natural number, not a real number.
`P` makes that type explicit, and `exact_reduction` reduces it to the
coefficient-one natural double tower. `exact_negation` expresses its negation
as strict counterexamples at arbitrarily large indices.

The final theorem is conditional on the proposed Ramsey recurrence, which
remains unproved. Its seed `R₃(4) ≤ 15` is supplied by `Submission.SmallRamsey`.
This module does not import `Submission.Spec` and does not use either of its
theorem declarations.
-/

namespace Erdos564.Reduction

open Combinatorics Filter

/-- The natural double tower appearing in the coefficient-one bound. -/
def tower (n : ℕ) : ℕ := 2 ^ (2 ^ n)

/-- The fixed proposition, with its inferred natural-number coefficient explicit. -/
def P : Prop :=
  ∃ c : ℕ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
    Real.rpow 2 ((2 : ℝ) ^ (c * n)) ≤ (hypergraphRamsey 3 n : ℝ)

/-- The outer real power is exactly the cast of a natural double tower. -/
theorem doublePow_cast (n : ℕ) :
    Real.rpow 2 ((2 : ℝ) ^ n) = (tower n : ℝ) := by
  change (2 : ℝ) ^ ((2 : ℝ) ^ n) = ((2 ^ (2 ^ n) : ℕ) : ℝ)
  have h : (2 : ℝ) ^ n = ((2 ^ n : ℕ) : ℝ) := by norm_cast
  rw [h, Real.rpow_natCast]
  norm_cast

/-- Positive natural coefficients are at least one; conversely, one is admissible. -/
theorem exact_reduction :
    P ↔ ∀ᶠ n : ℕ in atTop, tower n ≤ hypergraphRamsey 3 n := by
  constructor
  · rintro ⟨c, hc, h⟩
    filter_upwards [h] with n hn
    have hmul : n ≤ c * n := by
      simpa using Nat.mul_le_mul_right n (Nat.succ_le_of_lt hc)
    have hinner : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ (c * n) :=
      pow_le_pow_right₀ (by norm_num) hmul
    have houter : Real.rpow 2 ((2 : ℝ) ^ n) ≤
        Real.rpow 2 ((2 : ℝ) ^ (c * n)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hinner
    have hreal := houter.trans hn
    rw [doublePow_cast] at hreal
    exact_mod_cast hreal
  · intro h
    refine ⟨1, by decide, ?_⟩
    filter_upwards [h] with n hn
    simp only [one_mul, doublePow_cast]
    exact_mod_cast hn

/-- Exact negation: a strict counterexample exists beyond every natural threshold. -/
theorem exact_negation :
    ¬ P ↔ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ hypergraphRamsey 3 n < tower n := by
  classical
  rw [exact_reduction, eventually_atTop]
  simp only [not_exists, not_forall, exists_prop, not_le]

/-- The potential for the recurrence with the extra factor two.
It is `g(n) + 1`, where `g(n) = (n + 1).choose 2 + 1`. -/
def recurrencePotential (n : ℕ) : ℕ := (n + 1).choose 2 + 2

/-- Weight exponents exactly compensate for one recurrence step. -/
lemma recurrencePotential_identity (n : ℕ) :
    n.choose 2 + 1 + recurrencePotential (n + 1) = recurrencePotential n * 2 := by
  have h₁ : (n + 1).choose 2 = n + n.choose 2 := by
    simpa using Nat.choose_succ_succ n 1
  have h₂ : (n + 2).choose 2 = (n + 1) + (n + 1).choose 2 := by
    simpa using Nat.choose_succ_succ (n + 1) 1
  simp only [recurrencePotential]
  rw [show n + 1 + 1 = n + 2 by omega, h₂, h₁]
  omega

/-- The proposed numerical recurrence becomes squaring after weighting. -/
lemma weighted_step (f : ℕ → ℕ) (n : ℕ)
    (h : f (n + 1) ≤ 2 ^ (n.choose 2 + 1) * f n ^ 2) :
    f (n + 1) * 2 ^ recurrencePotential (n + 1) ≤
      (f n * 2 ^ recurrencePotential n) ^ 2 := by
  calc
    f (n + 1) * 2 ^ recurrencePotential (n + 1)
        ≤ (2 ^ (n.choose 2 + 1) * f n ^ 2) *
            2 ^ recurrencePotential (n + 1) := Nat.mul_le_mul_right _ h
    _ = f n ^ 2 * 2 ^ (n.choose 2 + 1 + recurrencePotential (n + 1)) := by
      rw [pow_add]
      ring
    _ = (f n * 2 ^ recurrencePotential n) ^ 2 := by
      rw [recurrencePotential_identity, pow_mul, mul_pow]

/-- A strictly subcritical weighted seed stays below the tower under the recurrence. -/
theorem below_tower_of_weighted_seed (f : ℕ → ℕ)
    (hseed : f 4 * 2 ^ recurrencePotential 4 < tower 4)
    (hrec : ∀ n : ℕ, 4 ≤ n →
      f (n + 1) ≤ 2 ^ (n.choose 2 + 1) * f n ^ 2) :
    ∀ n : ℕ, 4 ≤ n → f n < tower n := by
  have hweighted : ∀ n : ℕ, 4 ≤ n →
      f n * 2 ^ recurrencePotential n < tower n := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => exact hseed
    | succ n hn ih =>
      calc
        f (n + 1) * 2 ^ recurrencePotential (n + 1)
            ≤ (f n * 2 ^ recurrencePotential n) ^ 2 :=
              weighted_step f n (hrec n hn)
        _ < (tower n) ^ 2 := Nat.pow_lt_pow_left ih (by decide)
        _ = tower (n + 1) := by
          simp only [tower]
          rw [← pow_mul, pow_succ]
  intro n hn
  have hfactor : 1 ≤ 2 ^ recurrencePotential n := Nat.one_le_pow _ _ (by decide)
  have hmul : f n ≤ f n * 2 ^ recurrencePotential n := by
    calc
      f n = f n * 1 := by simp
      _ ≤ f n * 2 ^ recurrencePotential n := Nat.mul_le_mul_left _ hfactor
  exact lt_of_le_of_lt hmul (hweighted n hn)

/-- The seed 13 suffices even with the extra factor two at every step:
`13 * 2^12 = 53248 < 65536 = 2^(2^4)`. -/
theorem below_tower_of_recurrence (f : ℕ → ℕ) (hseed : f 4 ≤ 13)
    (hrec : ∀ n : ℕ, 4 ≤ n →
      f (n + 1) ≤ 2 ^ (n.choose 2 + 1) * f n ^ 2) :
    ∀ n : ℕ, 4 ≤ n → f n < tower n := by
  apply below_tower_of_weighted_seed f
  · have hpotential : recurrencePotential 4 = 12 := by decide
    have h := Nat.mul_le_mul_right (2 ^ recurrencePotential 4) hseed
    rw [hpotential] at h ⊢
    norm_num [tower] at h ⊢
    omega
  · exact hrec

/-- Conditional sufficiency only. The seed and the new recurrence are precisely
its mathematical hypotheses; this theorem proves neither of them. -/
theorem not_P_of_recurrence
    (hseed : hypergraphRamsey 3 4 ≤ 13)
    (hrec : ∀ n : ℕ, 4 ≤ n →
      hypergraphRamsey 3 (n + 1) ≤
        2 ^ (n.choose 2 + 1) * (hypergraphRamsey 3 n) ^ 2) :
    ¬ P := by
  apply exact_negation.mpr
  intro N
  refine ⟨max N 4, le_max_left _ _, ?_⟩
  exact below_tower_of_recurrence (hypergraphRamsey 3) hseed hrec
    (max N 4) (le_max_right _ _)

/-- The structural seed of fifteen eliminates the separate seed hypothesis.
The sole remaining hypothesis is the proposed recurrence, not established here. -/
theorem not_P_of_proposed_recurrence
    (hrec : ∀ n : ℕ, 4 ≤ n →
      hypergraphRamsey 3 (n + 1) ≤
        2 ^ (n.choose 2 + 1) * (hypergraphRamsey 3 n) ^ 2) :
    ¬ P := by
  have hseed : hypergraphRamsey 3 4 * 2 ^ recurrencePotential 4 < tower 4 := by
    have hp : recurrencePotential 4 = 12 := by decide
    simpa only [hp, tower] using Combinatorics.SmallRamsey.weighted_seed
  apply exact_negation.mpr
  intro N
  refine ⟨max N 4, le_max_left _ _, ?_⟩
  exact below_tower_of_weighted_seed (hypergraphRamsey 3) hseed hrec
    (max N 4) (le_max_right _ _)

end Erdos564.Reduction
