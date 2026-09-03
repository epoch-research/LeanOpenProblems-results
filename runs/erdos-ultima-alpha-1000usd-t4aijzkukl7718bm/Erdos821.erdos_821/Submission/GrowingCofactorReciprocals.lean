import Submission.PrimePairReciprocals

/-!
# Reciprocal convergence with a growing cofactor cutoff

For each fixed R, prime parents p=a*q+1 with prime q and
 a <= 2^(R*sqrt(floor(log_2 p)))
have finite reciprocal mass. This is a uniform growing-cutoff consequence of
the averaged two-prime sieve, not a proof of the arbitrary-root conjecture.
-/

open Nat Finset Filter
open scoped Classical BigOperators

namespace Erdos821

set_option maxHeartbeats 3000000

lemma bounded_cofactor_parent_count_le_pairs (N A : ℕ) :
    ((range N).filter (fun p => p ∈ boundedCofactorParentSet A)).card ≤
      ∑ a ∈ Icc 1 A,
        ((range (N/a+1)).filter (fun q => q.Prime ∧ (a*q+1).Prime)).card := by
  classical
  let Q : ℕ → Finset ℕ := fun a =>
    (range (N/a+1)).filter (fun q => q.Prime ∧ (a*q+1).Prime)
  have hsub : (range N).filter (fun p => p ∈ boundedCofactorParentSet A) ⊆
      (Icc 1 A).biUnion (fun a => (Q a).image (fun q => a*q+1)) := by
    intro p hp
    obtain ⟨hpN, a, ha, q, hq, heq⟩ := mem_filter.mp hp
    have ha0 : 0 < a := (mem_Icc.mp ha).1
    have hpN' : p < N := mem_range.mp hpN
    have hqN : q ≤ N/a := (Nat.le_div_iff_mul_le ha0).mpr (by nlinarith only [heq, hpN'])
    exact mem_biUnion.mpr ⟨a, ha, mem_image.mpr ⟨q,
      mem_filter.mpr ⟨mem_range.mpr (by omega), hq⟩, heq⟩⟩
  exact (card_le_card hsub).trans
    (card_biUnion_le.trans (sum_le_sum (fun _ _ => card_image_le)))

lemma cofactor_sieve_normalized_error (A m : ℕ) (hA : A ≤ 2^m) :
    (A : ℝ)*((2 : ℝ)^(64*m)+(2 : ℝ)^(16*m)+1)/(2 : ℝ)^(128*m) ≤
      3*(1/2 : ℝ)^m := by
  have hA' : (A : ℝ) ≤ (2 : ℝ)^(63*m) := by
    exact_mod_cast hA.trans (Nat.pow_le_pow_right (by decide) (by omega : m ≤ 63*m))
  have h16 : (2 : ℝ)^(16*m) ≤ (2 : ℝ)^(64*m) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have h1 : (1 : ℝ) ≤ (2 : ℝ)^(64*m) := one_le_pow₀ (by norm_num)
  have hE : (2 : ℝ)^(64*m)+(2 : ℝ)^(16*m)+1 ≤ 3*(2 : ℝ)^(64*m) := by linarith
  have hprod : (A : ℝ)*((2 : ℝ)^(64*m)+(2 : ℝ)^(16*m)+1) ≤ 3*(2 : ℝ)^(127*m) := by
    calc
      _ ≤ (2 : ℝ)^(63*m)*(3*(2 : ℝ)^(64*m)) :=
        mul_le_mul hA' hE (by positivity) (by positivity)
      _ = _ := by rw [mul_left_comm, ← pow_add]; congr 2; ring
  refine (div_le_div_of_nonneg_right hprod (by positivity)).trans_eq ?_
  rw [mul_div_assoc, pow_mul (2 : ℝ) 127 m, pow_mul (2 : ℝ) 128 m, ← div_pow]
  norm_num

noncomputable def cofactorSieveConstant : ℝ :=
  16*Sieve.totientRatioAverageConstant/(Real.log 2)^2

lemma cofactorSieveConstant_nonneg : 0 ≤ cofactorSieveConstant := by
  unfold cofactorSieveConstant Sieve.totientRatioAverageConstant
  positivity

lemma bounded_cofactor_parent_normalized_count (A m : ℕ) (hm : 0 < m) (hA : A ≤ 2^m) :
    (((range (2^(128*m))).filter (fun p => p ∈ boundedCofactorParentSet A)).card : ℝ)/
      (2 : ℝ)^(128*m) ≤
        cofactorSieveConstant*(harmonic A : ℝ)/(m : ℝ)^2 + 3*(1/2 : ℝ)^m := by
  have hAN : A ≤ 2^(128*m) := hA.trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hc : (((range (2^(128*m))).filter (fun p => p ∈ boundedCofactorParentSet A)).card : ℝ) ≤
      ∑ a ∈ Icc 1 A,
        (((range (2^(128*m)/a+1)).filter (fun q => q.Prime ∧ (a*q+1).Prime)).card : ℝ) := by
    exact_mod_cast bounded_cofactor_parent_count_le_pairs (2^(128*m)) A
  have hs := hc.trans (Sieve.sum_prime_pair_explicit_bound (2^(128*m)) A m hAN hm)
  have hmain :
      (16*Sieve.totientRatioAverageConstant*((2^(128*m) : ℕ) : ℝ)*(harmonic A : ℝ)/
        ((m : ℝ)*Real.log 2)^2)/(2 : ℝ)^(128*m) =
      cofactorSieveConstant*(harmonic A : ℝ)/(m : ℝ)^2 := by
    unfold cofactorSieveConstant
    push_cast only [Nat.cast_pow, Nat.cast_ofNat]
    field_simp
  have hd := div_le_div_of_nonneg_right hs (by positivity : (0 : ℝ) ≤ (2 : ℝ)^(128*m))
  rw [add_div, hmain] at hd
  exact hd.trans (_root_.add_le_add le_rfl (cofactor_sieve_normalized_error A m hA))

def rootLogCofactorCutoff (R p : ℕ) : ℕ := 2^(R*Nat.sqrt (Nat.log 2 p))

noncomputable def rootLogCofactorParentSet (R : ℕ) : Set ℕ :=
  {p | p ∈ boundedCofactorParentSet (rootLogCofactorCutoff R p)}

lemma rootLogCofactorCutoff_mono (R : ℕ) : Monotone (rootLogCofactorCutoff R) := by
  intro p P hpP
  exact Nat.pow_le_pow_right (by decide)
    (Nat.mul_le_mul_left R (Nat.sqrt_le_sqrt (Nat.log_mono_right hpP)))

lemma boundedCofactorParentSet_mono : Monotone boundedCofactorParentSet := by
  intro A B hAB p hp
  obtain ⟨a, ha, hp⟩ := hp
  exact ⟨a, mem_Icc.mpr ⟨(mem_Icc.mp ha).1, (mem_Icc.mp ha).2.trans hAB⟩, hp⟩

lemma rootLogCofactorParent_count_le (R m : ℕ) :
    ((range (2^(128*m))).filter (fun p => p ∈ rootLogCofactorParentSet R)).card ≤
      ((range (2^(128*m))).filter
        (fun p => p ∈ boundedCofactorParentSet (2^(R*Nat.sqrt (128*m))))).card := by
  apply card_le_card
  intro p hp
  obtain ⟨hpN, hpR⟩ := mem_filter.mp hp
  have hcut := rootLogCofactorCutoff_mono R (mem_range.mp hpN).le
  simp only [rootLogCofactorCutoff, Nat.log_pow (by decide : 1 < 2)] at hcut
  exact mem_filter.mpr ⟨hpN, boundedCofactorParentSet_mono hcut hpR⟩

lemma rootLog_block_cutoff_le (R m : ℕ) (hm : 128*R^2 ≤ m) :
    2^(R*Nat.sqrt (128*m)) ≤ 2^m := by
  apply Nat.pow_le_pow_right (by decide)
  apply (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp
  have hs := Nat.sqrt_le' (128*m)
  calc
    (R*Nat.sqrt (128*m))^2 = R^2*(Nat.sqrt (128*m))^2 := mul_pow _ _ _
    _ ≤ R^2*(128*m) := Nat.mul_le_mul_left _ hs
    _ ≤ m^2 := by nlinarith only [Nat.mul_le_mul_right m hm]

lemma harmonic_rootLog_block_le (R m : ℕ) (hm : 1 ≤ m) :
    (harmonic (2^(R*Nat.sqrt (128*m))) : ℝ) ≤ (1+16*(R : ℝ))*Real.sqrt (m : ℝ) := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hs1 : 1 ≤ Real.sqrt (m : ℝ) := Real.one_le_sqrt.mpr hmR
  have hs0 : 0 ≤ Real.sqrt (m : ℝ) := Real.sqrt_nonneg _
  have hs2 : (Real.sqrt (m : ℝ))^2 = m := Real.sq_sqrt (Nat.cast_nonneg _)
  have hk2 : ((Nat.sqrt (128*m) : ℕ) : ℝ)^2 ≤ 128*(m : ℝ) := by
    exact_mod_cast Nat.sqrt_le' (128*m)
  have hk : ((Nat.sqrt (128*m) : ℕ) : ℝ) ≤ 16*Real.sqrt (m : ℝ) := by
    nlinarith only [hk2, hs2, hs0, Nat.cast_nonneg (α := ℝ) (Nat.sqrt (128*m))]
  have hlog : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hH := harmonic_le_one_add_log (2^(R*Nat.sqrt (128*m)))
  rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow, Nat.cast_mul] at hH
  have hR : (0 : ℝ) ≤ R := Nat.cast_nonneg _
  have hlogmul := mul_le_mul_of_nonneg_left hlog
    (mul_nonneg hR (Nat.cast_nonneg (Nat.sqrt (128*m))))
  have hkmul := mul_le_mul_of_nonneg_left hk hR
  nlinarith only [hH, hlogmul, hkmul, hs1]

lemma sqrt_div_sq_eq_rpow (m : ℕ) (hm : 0 < m) :
    Real.sqrt (m : ℝ)/(m : ℝ)^2 = (m : ℝ)^(-3/2 : ℝ) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (m : ℝ) 2,
    ← Real.rpow_sub (by exact_mod_cast hm)]
  norm_num

lemma rootLog_cofactor_normalized_count (R m : ℕ) (hm : 1 ≤ m) (hRm : 128*R^2 ≤ m) :
    (((range (2^(128*m))).filter (fun p => p ∈ rootLogCofactorParentSet R)).card : ℝ)/
      (2 : ℝ)^(128*m) ≤
        (cofactorSieveConstant*(1+16*(R : ℝ)))*(m : ℝ)^(-3/2 : ℝ) +
          3*(1/2 : ℝ)^m := by
  have hc := div_le_div_of_nonneg_right
    (Nat.cast_le.mpr (rootLogCofactorParent_count_le R m))
    (by positivity : (0 : ℝ) ≤ (2 : ℝ)^(128*m))
  have hb := bounded_cofactor_parent_normalized_count (2^(R*Nat.sqrt (128*m))) m
    (by omega) (rootLog_block_cutoff_le R m hRm)
  refine (hc.trans hb).trans (_root_.add_le_add ?_ le_rfl)
  calc
    _ ≤ cofactorSieveConstant*((1+16*(R : ℝ))*Real.sqrt (m : ℝ))/(m : ℝ)^2 :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (harmonic_rootLog_block_le R m hm) cofactorSieveConstant_nonneg)
        (sq_nonneg _)
    _ = _ := by
      simp only [mul_div_assoc, sqrt_div_sq_eq_rpow m (by omega)]
      ring

/-- Cofactors may grow as exp(C*sqrt(log p)), with each fixed C, while the
prime parents still have a convergent reciprocal series. -/
theorem summable_rootLog_cofactor_parent_reciprocal (R : ℕ) :
    Summable ((rootLogCofactorParentSet R).indicator (fun p : ℕ => 1/(p : ℝ))) := by
  apply summable_reciprocal_of_summable_geometric_count (rootLogCofactorParentSet R) 128 (by decide)
  have hp : Summable (fun m : ℕ => (m : ℝ)^(-3/2 : ℝ)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hg : Summable (fun m : ℕ => (1/2 : ℝ)^m) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  apply ((hp.mul_left (cofactorSieveConstant*(1+16*(R : ℝ)))).add
    (hg.mul_left 3)).of_norm_bounded_eventually_nat
  filter_upwards [eventually_ge_atTop (max 1 (128*R^2))] with m hm
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) (by positivity))]
  exact rootLog_cofactor_normalized_count R m ((le_max_left _ _).trans hm)
    ((le_max_right _ _).trans hm)

/-- Removing the growing-cofactor parents leaves reciprocal divergence among
primes. This is only a near-full-size prime-factor bound, not root smoothness. -/
theorem not_summable_reciprocal_outside_rootLog_cofactor_parents (R : ℕ) :
    ¬Summable (({p : ℕ | p.Prime ∧ p ∉ rootLogCofactorParentSet R} : Set ℕ).indicator
      (fun p : ℕ => 1/(p : ℝ))) := by
  have H := summable_rootLog_cofactor_parent_reciprocal R
  simpa only [Real.rpow_neg_one, one_div] using
    not_summable_prime_complement_power_one (rootLogCofactorParentSet R) 1 (by norm_num)
      (by simpa only [Real.rpow_neg_one, one_div] using H)

lemma prime_outside_rootLog_cofactor_parent_iff (R p : ℕ) (hp : p.Prime) :
    p ∉ rootLogCofactorParentSet R ↔
      ∀ q ∈ (p-1).primeFactors, rootLogCofactorCutoff R p*q < p-1 := by
  have hp0 : 0 < p-1 := by have := hp.two_le; omega
  constructor
  · intro hout q hq
    have hqp := Nat.prime_of_mem_primeFactors hq
    have hqd := Nat.dvd_of_mem_primeFactors hq
    let a := (p-1)/q
    have ha : 0 < a := Nat.div_pos (Nat.le_of_dvd hp0 hqd) hqp.pos
    have heq : a*q = p-1 := Nat.div_mul_cancel hqd
    have hpEq : a*q+1 = p := by have := hp.two_le; omega
    have hlarge : rootLogCofactorCutoff R p < a := by
      by_contra h
      have haA : a ≤ rootLogCofactorCutoff R p := by omega
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

/-- In arithmetic form, the complementary primes retain reciprocal divergence
while every predecessor factor q satisfies q*cutoff(p)<p-1. -/
theorem not_summable_rootLog_prime_factor_bound (R : ℕ) :
    ¬Summable (({p : ℕ | p.Prime ∧
      ∀ q ∈ (p-1).primeFactors, rootLogCofactorCutoff R p*q < p-1} : Set ℕ).indicator
        (fun p : ℕ => 1/(p : ℝ))) := by
  have hsets : ({p : ℕ | p.Prime ∧ p ∉ rootLogCofactorParentSet R} : Set ℕ) =
      {p : ℕ | p.Prime ∧ ∀ q ∈ (p-1).primeFactors, rootLogCofactorCutoff R p*q < p-1} := by
    ext p
    constructor
    · intro hp
      exact ⟨hp.1, (prime_outside_rootLog_cofactor_parent_iff R p hp.1).mp hp.2⟩
    · intro hp
      exact ⟨hp.1, (prime_outside_rootLog_cofactor_parent_iff R p hp.1).mpr hp.2⟩
  rw [← hsets]
  exact not_summable_reciprocal_outside_rootLog_cofactor_parents R

end Erdos821
