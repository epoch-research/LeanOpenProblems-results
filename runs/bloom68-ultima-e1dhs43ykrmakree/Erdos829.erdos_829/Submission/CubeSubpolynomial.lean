import Submission.CubeCounting

/-!
# Subpolynomial upper bounds for sums of two cubes

This development proves the unconditional bound `sumRep cubes n = O(n ^ ε)`
for every positive real `ε`.  It does not prove the polylogarithmic bound
in Erdős Problem 829, and does not import or modify `Submission.Spec`.
-/

open scoped BigOperators
open Asymptotics Filter

namespace CubeSubpolynomial

/-- A geometric sequence with base greater than one dominates `e + 1`,
uniformly for all natural exponents. Bernoulli's inequality suffices. -/
theorem exists_ge_one_bound_succ_mul_pow {a : ℝ} (ha : 1 < a) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ e : ℕ, (e : ℝ) + 1 ≤ C * a ^ e := by
  let C : ℝ := 1 + (a - 1)⁻¹
  have ha0 : 0 < a - 1 := sub_pos.mpr ha
  have hC : 1 ≤ C := le_add_of_nonneg_right (inv_nonneg.mpr ha0.le)
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hCa : 1 ≤ C * (a - 1) := by
    dsimp [C]
    rw [add_mul, one_mul, inv_mul_cancel₀ ha0.ne']
    linarith
  refine ⟨C, hC, fun e => ?_⟩
  calc
    (e : ℝ) + 1 = 1 + (e : ℝ) * 1 := by ring
    _ ≤ C + (e : ℝ) * (C * (a - 1)) :=
      add_le_add hC (mul_le_mul_of_nonneg_left hCa (Nat.cast_nonneg e))
    _ = C * (1 + (e : ℝ) * (a - 1)) := by ring
    _ ≤ C * a ^ e :=
      mul_le_mul_of_nonneg_left (one_add_mul_sub_le_pow (by linarith) e) hC0

/-- Only finitely many natural bases have `p ^ ε < 2` when `ε > 0`. -/
theorem exists_rpow_threshold {ε : ℝ} (hε : 0 < ε) :
    ∃ P : ℕ, ∀ p : ℕ, P ≤ p → (2 : ℝ) ≤ (p : ℝ) ^ ε := by
  exact tendsto_atTop_atTop.mp
    ((tendsto_rpow_atTop hε).comp (tendsto_natCast_atTop_atTop (R := ℝ))) 2

/-- The product of the `ε`-powers of the prime-power factors is `n ^ ε`. -/
theorem prod_primeFactors_rpow (n : ℕ) (hn : n ≠ 0) (ε : ℝ) :
    (∏ p ∈ n.primeFactors, ((p : ℝ) ^ ε) ^ n.factorization p) = (n : ℝ) ^ ε := by
  simp_rw [Real.rpow_pow_comm (Nat.cast_nonneg _) ε]
  rw [Real.finset_prod_rpow _ _ (fun p _ => pow_nonneg (Nat.cast_nonneg p) _) ε]
  have hprod : (∏ p ∈ n.primeFactors, (p : ℝ) ^ n.factorization p) = (n : ℝ) := by
    exact_mod_cast Nat.factorization_prod_pow_eq_self hn
  rw [hprod]

/-- An elementary pointwise divisor bound, with a constant independent of `n`.
The formula for the divisor count is split into finitely many small primes
and large primes whose `ε`-powers are at least two. -/
theorem exists_card_divisors_le_mul_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ n : ℕ, (n.divisors.card : ℝ) ≤ K * (n : ℝ) ^ ε := by
  obtain ⟨C, hC, hsmall⟩ :=
    exists_ge_one_bound_succ_mul_pow (Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) hε)
  obtain ⟨P, hP⟩ := exists_rpow_threshold hε
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  refine ⟨C ^ P, one_le_pow₀ hC, fun n => ?_⟩
  by_cases hn : n = 0
  · simp [hn, Real.zero_rpow hε.ne']
  have hfactor (p : ℕ) (hp : p ∈ n.primeFactors) :
      (n.factorization p : ℝ) + 1 ≤
        (if p < P then C else 1) * ((p : ℝ) ^ ε) ^ n.factorization p := by
    have hp2 : (2 : ℝ) ≤ p := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    by_cases hlt : p < P
    · rw [if_pos hlt]
      exact (hsmall _).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (Real.rpow_nonneg (by norm_num) _)
          (Real.rpow_le_rpow (by norm_num) hp2 hε.le) _) hC0)
    · rw [if_neg hlt, one_mul]
      calc
        (n.factorization p : ℝ) + 1 ≤ (2 : ℝ) ^ n.factorization p := by
          exact_mod_cast (Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := n.factorization p)))
        _ ≤ ((p : ℝ) ^ ε) ^ n.factorization p :=
          pow_le_pow_left₀ (by norm_num) (hP p (Nat.le_of_not_gt hlt)) _
  have hconstant : (∏ p ∈ n.primeFactors, (if p < P then C else 1)) ≤ C ^ P := by
    rw [← Finset.prod_filter, Finset.prod_const]
    apply pow_le_pow_right₀ hC
    calc
      (n.primeFactors.filter (fun p => p < P)).card ≤ (Finset.range P).card :=
        Finset.card_le_card (fun p hp => Finset.mem_range.mpr (Finset.mem_filter.mp hp).2)
      _ = P := Finset.card_range P
  calc
    (n.divisors.card : ℝ) = ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1) := by
      rw [Nat.card_divisors hn, Nat.cast_prod]
      simp only [Nat.cast_add, Nat.cast_one]
    _ ≤ ∏ p ∈ n.primeFactors,
        ((if p < P then C else 1) * ((p : ℝ) ^ ε) ^ n.factorization p) :=
      Finset.prod_le_prod (fun p _ => by positivity) hfactor
    _ = (∏ p ∈ n.primeFactors, (if p < P then C else 1)) * (n : ℝ) ^ ε := by
      rw [Finset.prod_mul_distrib, prod_primeFactors_rpow n hn ε]
    _ ≤ C ^ P * (n : ℝ) ^ ε :=
      mul_le_mul_of_nonneg_right hconstant (Real.rpow_nonneg (Nat.cast_nonneg n) ε)

/-- The divisor-counting function is `O(n ^ ε)` for every positive real `ε`. -/
theorem card_divisors_isBigO_rpow {ε : ℝ} (hε : 0 < ε) :
    (fun n : ℕ => (n.divisors.card : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ ε) := by
  obtain ⟨K, _, hK⟩ := exists_card_divisors_le_mul_rpow hε
  apply Asymptotics.IsBigO.of_bound K
  apply Filter.Eventually.of_forall
  intro n
  simpa only [Real.norm_natCast, Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) ε)]
    using hK n

/-- On the natural numbers, a smaller real power is little-o of a larger one. -/
theorem natCast_rpow_isLittleO {a b : ℝ} (hab : a < b) :
    (fun n : ℕ => (n : ℝ) ^ a) =o[atTop] (fun n : ℕ => (n : ℝ) ^ b) := by
  apply Asymptotics.isLittleO_of_tendsto'
  · filter_upwards [eventually_ne_atTop (0 : ℕ)] with n hn
    have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    exact fun h => ((Real.rpow_pos_of_pos hnpos b).ne' h).elim
  · have ht := (tendsto_rpow_neg_atTop (sub_pos.mpr hab)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    refine ht.congr' ?_
    filter_upwards [eventually_ne_atTop (0 : ℕ)] with n hn
    have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    simp only [Function.comp_apply, neg_sub, Real.rpow_sub hnpos]

/-- Applying the Big-O bound with `ε / 2` gives a little-o divisor bound. -/
theorem card_divisors_isLittleO_rpow {ε : ℝ} (hε : 0 < ε) :
    (fun n : ℕ => (n.divisors.card : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ ε) :=
  (card_divisors_isBigO_rpow (half_pos hε)).trans_isLittleO
    (natCast_rpow_isLittleO (half_lt_self hε))

end CubeSubpolynomial

namespace CubeCounting

/-- For positive targets the elementary two-to-one divisor encoding gives
an asymptotic bound by the divisor count. The target zero is irrelevant at infinity. -/
theorem sumRep_isBigO_card_divisors :
    (fun n : ℕ => (AdditiveCombinatorics.sumRep cubes n : ℝ)) =O[atTop]
      (fun n : ℕ => (n.divisors.card : ℝ)) := by
  apply Asymptotics.IsBigO.of_bound 2
  filter_upwards [eventually_ne_atTop (0 : ℕ)] with n hn
  simp only [Real.norm_natCast]
  exact_mod_cast sumRep_le_two_mul_card_divisors hn

/-- The unconditional subpolynomial bound for the ordered number of
representations as a sum of two natural cubes, for every positive real exponent.
Here the power on the right is `Real.rpow`, not a natural power.
This does not establish the conjectured polylogarithmic bound. -/
theorem sumRep_isBigO_rpow (ε : ℝ) (hε : 0 < ε) :
    (fun n : ℕ => (AdditiveCombinatorics.sumRep cubes n : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ ε) :=
  sumRep_isBigO_card_divisors.trans (CubeSubpolynomial.card_divisors_isBigO_rpow hε)

/-- The same cube representation count is in fact `o(n ^ ε)` for every
positive real `ε`, by the divisor bound with exponent `ε / 2`. -/
theorem sumRep_isLittleO_rpow (ε : ℝ) (hε : 0 < ε) :
    (fun n : ℕ => (AdditiveCombinatorics.sumRep cubes n : ℝ)) =o[atTop]
      (fun n : ℕ => (n : ℝ) ^ ε) :=
  sumRep_isBigO_card_divisors.trans_isLittleO (CubeSubpolynomial.card_divisors_isLittleO_rpow hε)

end CubeCounting

#print axioms CubeSubpolynomial.exists_card_divisors_le_mul_rpow
#print axioms CubeSubpolynomial.card_divisors_isBigO_rpow
#print axioms CubeSubpolynomial.card_divisors_isLittleO_rpow
#print axioms CubeCounting.sumRep_isBigO_rpow
#print axioms CubeCounting.sumRep_isLittleO_rpow
