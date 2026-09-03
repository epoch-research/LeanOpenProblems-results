import Submission.GrowingCofactorReciprocals
import Submission.PrimeModulusReciprocals

/-!
# A small radical support for the full prime-predecessor pool

This controls the union of prime factors of p-1 over all primes p<=X.
It is a support-size estimate, not a multiplicity amplification theorem.
-/

open Nat Finset Filter
open scoped Classical BigOperators Topology

namespace Erdos821.DensePredecessors

set_option maxHeartbeats 2000000

noncomputable def support (X : ℕ) : Finset ℕ :=
  (X+1).primesBelow.biUnion (fun p => (p-1).primeFactors)

noncomputable def radicalPool (X : ℕ) : ℕ := ∏ q ∈ support X, q

lemma mem_support (X q : ℕ) : q ∈ support X ↔
    ∃ p, p ≤ X ∧ p.Prime ∧ q ∈ (p-1).primeFactors := by
  simp only [support, mem_biUnion, Nat.mem_primesBelow]
  constructor
  · rintro ⟨p, ⟨hpX,hp⟩, hq⟩
    exact ⟨p, by omega, hp, hq⟩
  · rintro ⟨p, hpX, hp, hq⟩
    exact ⟨p, ⟨by omega,hp⟩, hq⟩

lemma support_prime {X q : ℕ} (hq : q ∈ support X) : q.Prime := by
  obtain ⟨p,_,_,hq⟩ := (mem_support X q).mp hq
  exact Nat.prime_of_mem_primeFactors hq

lemma support_le {X q : ℕ} (hq : q ∈ support X) : q ≤ X := by
  obtain ⟨p,hpX,hp,hq⟩ := (mem_support X q).mp hq
  exact (Nat.le_of_dvd (Nat.sub_pos_of_lt hp.one_lt)
    (Nat.dvd_of_mem_primeFactors hq)).trans ((Nat.sub_le p 1).trans hpX)

lemma support_card_le_pairs (X A Z : ℕ) (hZ : 0 < Z) (hX : X ≤ A*Z) :
    (support X).card ≤ Z + ∑ a ∈ Icc 1 A,
      ((range (X/a+1)).filter (fun q => q.Prime ∧ (a*q+1).Prime)).card := by
  let Q : ℕ → Finset ℕ := fun a =>
    (range (X/a+1)).filter (fun q => q.Prime ∧ (a*q+1).Prime)
  have hsub : support X ⊆ Icc 1 Z ∪ (Icc 1 A).biUnion Q := by
    intro q hq
    obtain ⟨p,hpX,hp,hqp⟩ := (mem_support X q).mp hq
    have hprime := Nat.prime_of_mem_primeFactors hqp
    by_cases hqZ : q ≤ Z
    · exact mem_union_left _ (mem_Icc.mpr ⟨hprime.pos,hqZ⟩)
    have hqd := Nat.dvd_of_mem_primeFactors hqp
    let a := (p-1)/q
    have ha : 0 < a := Nat.div_pos
      (Nat.le_of_dvd (Nat.sub_pos_of_lt hp.one_lt) hqd) hprime.pos
    have he : a*q = p-1 := Nat.div_mul_cancel hqd
    have haA : a ≤ A := by
      apply Nat.le_of_mul_le_mul_right (c := Z) _ hZ
      calc
        a*Z ≤ a*q := Nat.mul_le_mul_left a (by omega)
        _ ≤ X := by omega
        _ ≤ A*Z := hX
    have hqX : q ≤ X/a := (Nat.le_div_iff_mul_le ha).mpr (by
      rw [mul_comm q a,he]
      exact (Nat.sub_le p 1).trans hpX)
    apply mem_union_right
    apply mem_biUnion.mpr
    refine ⟨a,mem_Icc.mpr ⟨ha,haA⟩,?_⟩
    have hpEq : a*q+1 = p := by have := hp.two_le; omega
    exact mem_filter.mpr ⟨mem_range.mpr (by omega),hprime,hpEq.symm ▸ hp⟩
  calc
    _ ≤ (Icc 1 Z ∪ (Icc 1 A).biUnion Q).card := card_le_card hsub
    _ ≤ (Icc 1 Z).card + ((Icc 1 A).biUnion Q).card := card_union_le _ _
    _ ≤ _ := by simpa only [Nat.card_Icc, Nat.add_sub_cancel] using
      Nat.add_le_add_left (card_biUnion_le (s := Icc 1 A) (t := Q)) Z

lemma pair_sum_normalized_le (A m : ℕ) (hm : 0 < m) (hA : A ≤ 2^m) :
    (∑ a ∈ Icc 1 A,
      (((range (2^(128*m)/a+1)).filter (fun q => q.Prime ∧ (a*q+1).Prime)).card : ℝ)) /
      (2 : ℝ)^(128*m) ≤
        cofactorSieveConstant*(harmonic A : ℝ)/(m : ℝ)^2 + 3*(1/2 : ℝ)^m := by
  have hAN : A ≤ 2^(128*m) := hA.trans
    (Nat.pow_le_pow_right (by decide) (by omega))
  have hs := Sieve.sum_prime_pair_explicit_bound (2^(128*m)) A m hAN hm
  have hd := div_le_div_of_nonneg_right hs (by positivity : (0 : ℝ) ≤ (2 : ℝ)^(128*m))
  have hmain :
      (16*Sieve.totientRatioAverageConstant*((2^(128*m) : ℕ) : ℝ)*(harmonic A : ℝ)/
        ((m : ℝ)*Real.log 2)^2)/(2 : ℝ)^(128*m) =
      cofactorSieveConstant*(harmonic A : ℝ)/(m : ℝ)^2 := by
    unfold cofactorSieveConstant
    push_cast only [Nat.cast_pow, Nat.cast_ofNat]
    field_simp
  rw [add_div,hmain] at hd
  exact hd.trans (add_le_add le_rfl (cofactor_sieve_normalized_error A m hA))

lemma harmonic_two_pow_le (m : ℕ) : (harmonic (2^m) : ℝ) ≤ 1+m := by
  have h := harmonic_le_one_add_log (2^m)
  rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] at h
  have hlog : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  nlinarith [mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg m)]

/-- The square in the scale makes the logarithmic support bound tend to zero
using only the available two-prime sieve. -/
theorem scaled_support_bound (m : ℕ) (hm : 1 ≤ m) :
    (m : ℝ)^2 * (support (2^(128*m^2))).card / (2 : ℝ)^(128*m^2) ≤
      cofactorSieveConstant*((m : ℝ)⁻¹^2+(m : ℝ)⁻¹) +
        4*(m : ℝ)^2*(1/2 : ℝ)^m := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hmm : m ≤ m^2 := by nlinarith
  have hdiff : m ≤ 128*m^2 := by omega
  have hpow : 2^m * 2^(128*m^2-m) = (2 : ℕ)^(128*m^2) := by
    rw [← pow_add, Nat.add_sub_of_le hdiff]
  have hc := support_card_le_pairs (2^(128*m^2)) (2^m) (2^(128*m^2-m))
    (by positivity) (by rw [hpow])
  have hcR : ((support (2^(128*m^2))).card : ℝ) ≤
      (2 : ℝ)^(128*m^2-m) + ∑ a ∈ Icc 1 (2^m),
        (((range (2^(128*m^2)/a+1)).filter (fun q => q.Prime ∧ (a*q+1).Prime)).card : ℝ) := by
    exact_mod_cast hc
  have hd := div_le_div_of_nonneg_right hcR (by positivity : (0 : ℝ) ≤ (2 : ℝ)^(128*m^2))
  rw [add_div] at hd
  have hb := pair_sum_normalized_le (2^m) (m^2) (by positivity)
    (Nat.pow_le_pow_right (by decide) hmm)
  have hratio : (2 : ℝ)^(128*m^2-m)/(2 : ℝ)^(128*m^2) = (1/2 : ℝ)^m := by
    have he : (2 : ℝ)^(128*m^2) = (2 : ℝ)^m*(2 : ℝ)^(128*m^2-m) := by
      exact_mod_cast hpow.symm
    rw [he, div_pow, one_pow]
    field_simp
  rw [hratio] at hd
  have hsmall : (1/2 : ℝ)^(m^2) ≤ (1/2 : ℝ)^m :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hmm
  have hH := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (harmonic_two_pow_le m) cofactorSieveConstant_nonneg)
    (sq_nonneg ((m^2 : ℕ) : ℝ))
  have ht := hd.trans (_root_.add_le_add le_rfl (hb.trans (_root_.add_le_add hH
    (mul_le_mul_of_nonneg_left hsmall (by norm_num)))))
  have ht' := mul_le_mul_of_nonneg_left ht (sq_nonneg (m : ℝ))
  convert ht' using 1 <;> push_cast <;> field_simp [hm0]
  ring

lemma radicalPool_pos (X : ℕ) : 0 < radicalPool X :=
  prod_pos (fun _ hq => (support_prime hq).pos)

lemma log_radicalPool_le (X : ℕ) :
    Real.log (radicalPool X : ℝ) ≤ (support X).card * Real.log X := by
  unfold radicalPool
  rw [Nat.cast_prod, Real.log_prod (fun q hq => by
    exact_mod_cast (support_prime hq).ne_zero)]
  calc
    _ ≤ ∑ _q ∈ support X, Real.log X := sum_le_sum (fun q hq =>
      Real.log_le_log (by exact_mod_cast (support_prime hq).pos)
        (by exact_mod_cast support_le hq))
    _ = _ := by simp

/-- The number of distinct predecessor labels is o(X/log X) on this
sequence of cutoffs. -/
theorem tendsto_scaled_support :
    Tendsto (fun m : ℕ => (m : ℝ)^2 * (support (2^(128*m^2))).card /
      (2 : ℝ)^(128*m^2)) atTop (𝓝 0) := by
  have hi : Tendsto (fun m : ℕ => (m : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hg := tendsto_pow_const_mul_const_pow_of_lt_one 2
    (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) < 1)
  have ht : Tendsto (fun m : ℕ =>
      cofactorSieveConstant*((m : ℝ)⁻¹^2+(m : ℝ)⁻¹) +
        4*(m : ℝ)^2*(1/2 : ℝ)^m) atTop (𝓝 0) := by
    simpa only [zero_pow (by decide : 2 ≠ 0), zero_add, mul_zero, add_zero, mul_assoc]
      using (((hi.pow 2).add hi).const_mul cofactorSieveConstant).add (hg.const_mul 4)
  apply squeeze_zero' (Eventually.of_forall (fun _ => by positivity)) _ ht
  filter_upwards [eventually_ge_atTop 1] with m hm
  exact scaled_support_bound m hm

/-- The common radical support of the full prime pool has logarithm o(X).
This alone does not compare its size to a sparse selected subfamily's output. -/
theorem tendsto_log_radicalPool_div :
    Tendsto (fun m : ℕ => Real.log (radicalPool (2^(128*m^2)) : ℝ) /
      (2 : ℝ)^(128*m^2)) atTop (𝓝 0) := by
  have ht : Tendsto (fun m : ℕ => (128*Real.log 2)*
      ((m : ℝ)^2*(support (2^(128*m^2))).card/(2 : ℝ)^(128*m^2))) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_scaled_support.const_mul (128*Real.log 2)
  apply squeeze_zero (fun m => div_nonneg (Real.log_nonneg (by
    exact_mod_cast (radicalPool_pos (2^(128*m^2))))) (by positivity)) _ ht
  intro m
  have h := div_le_div_of_nonneg_right (log_radicalPool_le (2^(128*m^2)))
    (by positivity : (0 : ℝ) ≤ (2 : ℝ)^(128*m^2))
  apply h.trans_eq
  rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  push_cast
  ring

/-- A subexponential bound at the full prime-pool scale. No assertion about
inverse-totient multiplicities is made. -/
theorem eventually_radicalPool_le_exp (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, (radicalPool (2^(128*m^2)) : ℝ) ≤
      Real.exp (ε*(2 : ℝ)^(128*m^2)) := by
  filter_upwards [tendsto_log_radicalPool_div.eventually_lt_const hε] with m hm
  have hp : (0 : ℝ) < radicalPool (2^(128*m^2)) := by
    exact_mod_cast radicalPool_pos (2^(128*m^2))
  rw [← Real.exp_log hp]
  apply Real.exp_le_exp.mpr
  exact ((div_lt_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ)^(128*m^2))).mp hm).le


noncomputable def predecessorProduct (X : ℕ) : ℕ :=
  ∏ p ∈ (X+1).primesBelow, (p-1)

lemma predecessorProduct_pos (X : ℕ) : 0 < predecessorProduct X := by
  apply prod_pos
  intro p hp
  exact Nat.sub_pos_of_lt (Nat.mem_primesBelow.mp hp).2.one_lt

lemma predecessorProduct_primeFactors (X : ℕ) :
    (predecessorProduct X).primeFactors = support X := by
  ext q
  constructor
  · intro hq
    have hprime := Nat.prime_of_mem_primeFactors hq
    obtain ⟨p,hp,hqp⟩ := (hprime.prime.dvd_finset_prod_iff (fun p : ℕ => p-1)).mp
      (Nat.dvd_of_mem_primeFactors hq)
    obtain ⟨hpX,hpr⟩ := Nat.mem_primesBelow.mp hp
    exact (mem_support X q).mpr ⟨p,by omega,hpr,
      hprime.mem_primeFactors hqp (Nat.sub_pos_of_lt hpr.one_lt).ne'⟩
  · intro hq
    obtain ⟨p,hpX,hp,hqp⟩ := (mem_support X q).mp hq
    have hpP : p ∈ (X+1).primesBelow := Nat.mem_primesBelow.mpr ⟨by omega,hp⟩
    exact (Nat.prime_of_mem_primeFactors hqp).mem_primeFactors
      ((Nat.dvd_of_mem_primeFactors hqp).trans (dvd_prod_of_mem (fun p : ℕ => p-1) hpP))
      (predecessorProduct_pos X).ne'

lemma radicalPool_eq_radical_predecessorProduct (X : ℕ) :
    radicalPool X = ∏ q ∈ (predecessorProduct X).primeFactors, q := by
  rw [predecessorProduct_primeFactors]
  rfl

lemma predecessorProduct_eq_totient (X : ℕ) :
    predecessorProduct X = Nat.totient (∏ p ∈ (X+1).primesBelow, p) := by
  exact (totient_prod_primes _ (fun p hp => (Nat.mem_primesBelow.mp hp).2)).symm

lemma log_le_twice_log_pred (p : ℕ) (hp : 3 ≤ p) :
    Real.log p ≤ 2*Real.log ((p-1 : ℕ) : ℝ) := by
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hpred : (0 : ℝ) < ((p-1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < p-1 by omega)
  have hsq : (p : ℝ) ≤ ((p-1 : ℕ) : ℝ)^2 := by
    rw [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]
    nlinarith
  have h := Real.log_le_log (by linarith : (0 : ℝ) < p) hsq
  simpa only [Real.log_pow, Nat.cast_ofNat] using h

lemma theta_le_twice_log_predecessorProduct (X : ℕ) (hX : 2 ≤ X) :
    Chebyshev.theta X ≤ 2*Real.log (predecessorProduct X : ℝ)+Real.log 2 := by
  let P := (X+1).primesBelow
  have hP2 : 2 ∈ P := Nat.mem_primesBelow.mpr ⟨by omega,by decide⟩
  have he : Real.log (predecessorProduct X : ℝ) =
      ∑ p ∈ P.erase 2, Real.log ((p-1 : ℕ) : ℝ) := by
    unfold predecessorProduct
    rw [Nat.cast_prod, Real.log_prod (fun p hp => by
      exact_mod_cast (Nat.sub_pos_of_lt (Nat.mem_primesBelow.mp hp).2.one_lt).ne')]
    change (∑ p ∈ P, Real.log ((p-1 : ℕ) : ℝ)) = _
    rw [← sum_erase_add _ _ hP2]
    norm_num
  have hs : (∑ p ∈ P.erase 2, Real.log (p : ℝ)) ≤
      2*∑ p ∈ P.erase 2, Real.log ((p-1 : ℕ) : ℝ) := by
    rw [mul_sum]
    apply sum_le_sum
    intro p hp
    obtain ⟨hp2,hpP⟩ := mem_erase.mp hp
    have hpr := (Nat.mem_primesBelow.mp hpP).2.two_le
    exact log_le_twice_log_pred p (by omega)
  rw [Sieve.theta_nat_eq_sum_primesBelow]
  change (∑ p ∈ P, Real.log (p : ℝ)) ≤ _
  rw [← sum_erase_add _ _ hP2,he]
  exact _root_.add_le_add hs le_rfl

lemma log_predecessorProduct_lower (m : ℕ) (hm : 1 ≤ m) :
    (2 : ℝ)^(128*m^2)/64 ≤ Real.log (predecessorProduct (2^(128*m^2)) : ℝ) := by
  have htheta := AnalyticSieve.progression_scale_theta_lower
    (s := 2*m^2) (by nlinarith : 1 ≤ 2*m^2)
  have hexp : 64*(2*m^2) = 128*m^2 := by ring
  simp only [AnalyticSieve.progressionScaleN,hexp] at htheta
  have hX : (64 : ℕ) ≤ 2^(128*m^2) := by
    calc
      _ = 2^6 := by norm_num
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by nlinarith)
  have hXr : (64 : ℝ) ≤ (2 : ℝ)^(128*m^2) := by exact_mod_cast hX
  have h := theta_le_twice_log_predecessorProduct (2^(128*m^2)) (by omega)
  have hlog : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  push_cast at htheta h
  linarith

/-- For the full prime pool, its radical really is subpower relative to its
predecessor product. This is not asserted for sparse selected subfamilies. -/
theorem eventually_radicalPool_le_predecessorProduct_rpow (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, (radicalPool (2^(128*m^2)) : ℝ) ≤
      (predecessorProduct (2^(128*m^2)) : ℝ)^ε := by
  filter_upwards [tendsto_log_radicalPool_div.eventually_lt_const
    (by positivity : (0 : ℝ) < ε/64), eventually_ge_atTop 1] with m hm hm1
  have h1 := (div_lt_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ)^(128*m^2))).mp hm
  have h2 := mul_le_mul_of_nonneg_left (log_predecessorProduct_lower m hm1) hε.le
  have hlog : Real.log (radicalPool (2^(128*m^2)) : ℝ) ≤
      Real.log (predecessorProduct (2^(128*m^2)) : ℝ)*ε := by linarith
  have hR : (0 : ℝ) < radicalPool (2^(128*m^2)) := by
    exact_mod_cast radicalPool_pos (2^(128*m^2))
  have hN : (0 : ℝ) < predecessorProduct (2^(128*m^2)) := by
    exact_mod_cast predecessorProduct_pos (2^(128*m^2))
  rw [Real.rpow_def_of_pos hN, ← Real.exp_log hR]
  exact Real.exp_le_exp.mpr hlog

lemma support_subset_prime_pool (X : ℕ) : support X ⊆ (X+1).primesBelow := by
  intro q hq
  exact Nat.mem_primesBelow.mpr ⟨by have := support_le hq; omega, support_prime hq⟩

lemma totient_radicalPool_dvd_predecessorProduct (X : ℕ) :
    Nat.totient (radicalPool X) ∣ predecessorProduct X := by
  rw [radicalPool,totient_prod_primes _ (fun _ hq => support_prime hq)]
  exact prod_dvd_prod_of_subset _ _ _ (support_subset_prime_pool X)

/-- Every prime outside the common predecessor support is independently
optional in a preimage of the full predecessor product. -/
theorem two_pow_optional_primes_le_g (X : ℕ) :
    2^((X+1).primesBelow.card-(support X).card) ≤ g (predecessorProduct X) := by
  have h := two_pow_card_sdiff_le_g_prod_pred (X+1).primesBelow (support X)
    (fun _ hp => (Nat.mem_primesBelow.mp hp).2) (support_subset_prime_pool X)
    (fun p hp q hq => mem_biUnion.mpr ⟨p,hp,hq⟩)
  simpa only [card_sdiff_of_subset (support_subset_prime_pool X),predecessorProduct] using h

end Erdos821.DensePredecessors
