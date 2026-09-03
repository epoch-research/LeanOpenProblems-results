import Submission.GrowingCofactorReciprocals

/-!
# Variable-cofactor reciprocal criterion

A uniform consequence of the averaged two-prime sieve. The applications
below have subpower cofactor cutoffs; no fixed-root smoothness assertion
or contraction of the full prime-parent tree is claimed.
-/

open Nat Finset Filter
open scoped Classical BigOperators

namespace Erdos821

set_option maxHeartbeats 3000000

noncomputable def variableCofactorParentSet (A : ℕ → ℕ) : Set ℕ :=
  {p | p ∈ boundedCofactorParentSet (A p)}

lemma variableCofactorParent_count_le (A : ℕ → ℕ) (hA : Monotone A) (N : ℕ) :
    ((range N).filter (fun p => p ∈ variableCofactorParentSet A)).card ≤
      ((range N).filter (fun p => p ∈ boundedCofactorParentSet (A N))).card := by
  apply card_le_card
  intro p hp
  obtain ⟨hpN, hpA⟩ := mem_filter.mp hp
  exact mem_filter.mpr ⟨hpN,
    boundedCofactorParentSet_mono (hA (mem_range.mp hpN).le) hpA⟩

/-- Summability of harmonic cutoff costs on the geometric scales is enough
for reciprocal convergence of all the corresponding prime parents. -/
theorem summable_variable_cofactor_parent_reciprocal (A : ℕ → ℕ) (hA : Monotone A)
    (hsmall : ∀ᶠ m : ℕ in atTop, A (2^(128*m)) ≤ 2^m)
    (hsum : Summable (fun m : ℕ =>
      (harmonic (A (2^(128*m))) : ℝ)/(m : ℝ)^2)) :
    Summable ((variableCofactorParentSet A).indicator (fun p : ℕ => 1/(p : ℝ))) := by
  apply summable_reciprocal_of_summable_geometric_count
    (variableCofactorParentSet A) 128 (by decide)
  have hg : Summable (fun m : ℕ => (1/2 : ℝ)^m) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  apply ((hsum.mul_left cofactorSieveConstant).add (hg.mul_left 3)).of_norm_bounded_eventually_nat
  filter_upwards [hsmall, eventually_ge_atTop 1] with m hsm hm
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) (by positivity))]
  have hcount := div_le_div_of_nonneg_right
    (Nat.cast_le.mpr (variableCofactorParent_count_le A hA (2^(128*m))))
    (by positivity : (0 : ℝ) ≤ (2 : ℝ)^(128*m))
  exact (hcount.trans (bounded_cofactor_parent_normalized_count (A (2^(128*m))) m
    (by omega) hsm)).trans_eq (by ring)

noncomputable def stretchedLogCofactorCutoff (R β : ℝ) (p : ℕ) : ℕ :=
  2^(⌊R*(Nat.log 2 p : ℝ)^β⌋₊)

lemma stretchedLogCofactorCutoff_mono (R β : ℝ) (hR : 0 ≤ R) (hβ : 0 ≤ β) :
    Monotone (stretchedLogCofactorCutoff R β) := by
  intro p P hpP
  apply Nat.pow_le_pow_right (by decide)
  apply Nat.floor_mono
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.mpr (Nat.log_mono_right hpP)) hβ) hR

lemma eventually_stretchedLog_block_cutoff_le (R β : ℝ) (hβ : β < 1) :
    ∀ᶠ m : ℕ in atTop, stretchedLogCofactorCutoff R β (2^(128*m)) ≤ 2^m := by
  have ht := ((tendsto_rpow_neg_atTop (by linarith : 0 < 1-β)).comp
    tendsto_natCast_atTop_atTop).const_mul (R*(128 : ℝ)^β)
  simp only [mul_zero] at ht
  have he : -(1-β) = β-1 := by ring
  simp only [he, Function.comp_def] at ht
  filter_upwards [ht.eventually_lt_const (by norm_num : (0 : ℝ) < 1),
    eventually_ge_atTop 1] with m h hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  apply Nat.pow_le_pow_right (by decide)
  apply Nat.floor_le_of_le
  dsimp only [stretchedLogCofactorCutoff]
  rw [Nat.log_pow (by decide : 1 < 2), Nat.cast_mul, Nat.cast_ofNat,
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 128) hmR.le]
  rw [Real.rpow_sub hmR, Real.rpow_one, ← mul_div_assoc] at h
  have hh := (div_lt_one hmR).mp h
  nlinarith only [hh]

lemma harmonic_stretchedLog_block_le (R β : ℝ) (hR : 0 ≤ R) (hβ : 0 ≤ β)
    (m : ℕ) (hm : 1 ≤ m) :
    (harmonic (stretchedLogCofactorCutoff R β (2^(128*m))) : ℝ) ≤
      (1+R*(128 : ℝ)^β*Real.log 2)*(m : ℝ)^β := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have h1 := Real.one_le_rpow hmR hβ
  have hlog : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have hf := Nat.floor_le (mul_nonneg hR
    (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ (128 : ℝ)*(m : ℝ)) β))
  have hH := harmonic_le_one_add_log (stretchedLogCofactorCutoff R β (2^(128*m)))
  simp only [stretchedLogCofactorCutoff, Nat.log_pow (by decide : 1 < 2),
    Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, Real.log_pow] at hH
  have hfL := mul_le_mul_of_nonneg_right hf hlog
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 128) (Nat.cast_nonneg m)] at hfL
  simp only [stretchedLogCofactorCutoff, Nat.log_pow (by decide : 1 < 2),
    Nat.cast_mul, Nat.cast_ofNat]
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 128) (Nat.cast_nonneg m)] at hH ⊢
  nlinarith only [hH, hfL, h1]

lemma summable_stretchedLog_harmonic_cost (R β : ℝ) (hR : 0 ≤ R)
    (hβ : 0 ≤ β) (hβ1 : β < 1) :
    Summable (fun m : ℕ =>
      (harmonic (stretchedLogCofactorCutoff R β (2^(128*m))) : ℝ)/(m : ℝ)^2) := by
  have hs : Summable (fun m : ℕ => (m : ℝ)^(β-2)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  apply (hs.mul_left (1+R*(128 : ℝ)^β*Real.log 2)).of_norm_bounded_eventually_nat
  filter_upwards [eventually_ge_atTop 1] with m hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (by
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    positivity) (sq_nonneg _))]
  calc
    _ ≤ ((1+R*(128 : ℝ)^β*Real.log 2)*(m : ℝ)^β)/(m : ℝ)^2 :=
      div_le_div_of_nonneg_right (harmonic_stretchedLog_block_le R β hR hβ m hm) (sq_nonneg _)
    _ = _ := by
      rw [Real.rpow_sub hmR, Real.rpow_two, mul_div_assoc]

/-- For every fixed beta below one, these stretched-logarithmic cofactors
have a reciprocal-summable set of prime parents. -/
theorem summable_stretchedLog_cofactor_parent_reciprocal (R β : ℝ) (hR : 0 ≤ R)
    (hβ : 0 ≤ β) (hβ1 : β < 1) :
    Summable ((variableCofactorParentSet (stretchedLogCofactorCutoff R β)).indicator
      (fun p : ℕ => 1/(p : ℝ))) := by
  exact summable_variable_cofactor_parent_reciprocal _
    (stretchedLogCofactorCutoff_mono R β hR hβ)
    (eventually_stretchedLog_block_cutoff_le R β hβ1)
    (summable_stretchedLog_harmonic_cost R β hR hβ hβ1)

lemma prime_outside_variable_cofactor_parent_iff (A : ℕ → ℕ) (p : ℕ) (hp : p.Prime) :
    p ∉ variableCofactorParentSet A ↔
      ∀ q ∈ (p-1).primeFactors, A p*q < p-1 := by
  have hp0 : 0 < p-1 := by have := hp.two_le; omega
  constructor
  · intro hout q hq
    have hqp := Nat.prime_of_mem_primeFactors hq
    have hqd := Nat.dvd_of_mem_primeFactors hq
    let a := (p-1)/q
    have ha : 0 < a := Nat.div_pos (Nat.le_of_dvd hp0 hqd) hqp.pos
    have heq : a*q = p-1 := Nat.div_mul_cancel hqd
    have hpEq : a*q+1 = p := by have := hp.two_le; omega
    have hlarge : A p < a := by
      by_contra h
      have haA : a ≤ A p := by omega
      exact hout ⟨a, mem_Icc.mpr ⟨ha, haA⟩, q, ⟨hqp, hpEq.symm ▸ hp⟩, hpEq⟩
    simpa only [heq] using Nat.mul_lt_mul_of_pos_right hlarge hqp.pos
  · intro hfac hin
    obtain ⟨a, ha, q, hq, heq⟩ := hin
    change a*q+1 = p at heq
    have hqd : q ∣ p-1 := by
      rw [← heq, Nat.add_sub_cancel]
      exact dvd_mul_left q a
    have hqmem : q ∈ (p-1).primeFactors := hq.1.mem_primeFactors hqd hp0.ne'
    have hlt := hfac q hqmem
    have hle := Nat.mul_le_mul_right q (mem_Icc.mp ha).2
    have heq' : a*q = p-1 := by have := hp.two_le; omega
    omega

/-- In arithmetic form, the complementary primes retain divergent
reciprocal mass. The factor cutoff is not a fixed power of p. -/
theorem not_summable_stretchedLog_prime_factor_bound (R β : ℝ) (hR : 0 ≤ R)
    (hβ : 0 ≤ β) (hβ1 : β < 1) :
    ¬Summable (({p : ℕ | p.Prime ∧
      ∀ q ∈ (p-1).primeFactors, stretchedLogCofactorCutoff R β p*q < p-1} : Set ℕ).indicator
        (fun p : ℕ => 1/(p : ℝ))) := by
  have H := summable_stretchedLog_cofactor_parent_reciprocal R β hR hβ hβ1
  have hc := not_summable_prime_complement_power_one
    (variableCofactorParentSet (stretchedLogCofactorCutoff R β)) 1 (by norm_num)
    (by simpa only [Real.rpow_neg_one, one_div] using H)
  have hsets : ({p : ℕ | p.Prime ∧
      p ∉ variableCofactorParentSet (stretchedLogCofactorCutoff R β)} : Set ℕ) =
      {p : ℕ | p.Prime ∧ ∀ q ∈ (p-1).primeFactors, stretchedLogCofactorCutoff R β p*q < p-1} := by
    ext p
    constructor
    · intro hp
      exact ⟨hp.1, (prime_outside_variable_cofactor_parent_iff _ p hp.1).mp hp.2⟩
    · intro hp
      exact ⟨hp.1, (prime_outside_variable_cofactor_parent_iff _ p hp.1).mpr hp.2⟩
  simpa only [hsets, Real.rpow_neg_one, one_div] using hc

/-- At beta = 1 and positive R, the harmonic majorant in the criterion
is not summable. This is a boundary of this sufficient criterion only:
it is not a nonsummability assertion for the actual prime-parent set. -/
theorem not_summable_linearLog_harmonic_cost (R : ℝ) (hR : 0 < R) :
    ¬Summable (fun m : ℕ =>
      (harmonic (stretchedLogCofactorCutoff R 1 (2^(128*m))) : ℝ)/(m : ℝ)^2) := by
  intro H
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let C : ℝ := 64*R*Real.log 2
  have hC : 0 < C := by dsimp only [C]; positivity
  apply Real.not_summable_one_div_natCast
  apply (summable_mul_left_iff hC.ne').mp
  apply H.of_norm_bounded_eventually_nat
  obtain ⟨M, hM⟩ := exists_nat_ge (1/(64*R))
  filter_upwards [eventually_ge_atTop (max 1 M)] with m hm
  have hm0 : 0 < m := by omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hmM : (M : ℝ) ≤ m := by exact_mod_cast ((le_max_right 1 M).trans hm)
  have hm1 : 1 ≤ (64*R)*(m : ℝ) := by
    have h := (div_le_iff₀ (by positivity : (0 : ℝ) < 64*R)).mp (hM.trans hmM)
    nlinarith only [h]
  let j : ℕ := ⌊R*(128*(m : ℝ))⌋₊
  have hj : 64*R*(m : ℝ) ≤ (j : ℝ) := by
    have hf := Nat.lt_floor_add_one (R*(128*(m : ℝ)))
    dsimp only [j]
    nlinarith only [hf, hm1]
  have hH : (j : ℝ)*Real.log 2 ≤ (harmonic (2^j) : ℝ) := by
    have hpow : (0 : ℝ) < ((2^j : ℕ) : ℝ) := by positivity
    have hmono : Real.log ((2^j : ℕ) : ℝ) ≤ Real.log ((2^j+1 : ℕ) : ℝ) :=
      Real.log_le_log hpow (by exact_mod_cast (Nat.le_succ (2^j)))
    have h := hmono.trans (log_add_one_le_harmonic (2^j))
    simpa only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] using h
  have hlower : C*(m : ℝ) ≤ (harmonic (2^j) : ℝ) := by
    have h := (mul_le_mul_of_nonneg_right hj hlog.le).trans hH
    dsimp only [C]
    nlinarith only [h]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hC.le
    (div_nonneg (by norm_num) hmR.le)), mul_one_div]
  simp only [stretchedLogCofactorCutoff, Nat.log_pow (by decide : 1 < 2),
    Nat.cast_mul, Nat.cast_ofNat, Real.rpow_one]
  change C/(m : ℝ) ≤ (harmonic (2^j) : ℝ)/(m : ℝ)^2
  apply (div_le_div_iff₀ hmR (sq_pos_of_pos hmR)).mpr
  have h := mul_le_mul_of_nonneg_right hlower hmR.le
  nlinarith only [h]

end Erdos821
