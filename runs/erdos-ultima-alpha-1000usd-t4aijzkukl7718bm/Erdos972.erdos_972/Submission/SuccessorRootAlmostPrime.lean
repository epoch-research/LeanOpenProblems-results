import Submission.EfficientPrimeAlmostPrime

/-! Retaining the successor in the exact power-root bound improves the
proved output-factor bound from 49153 to 24576. This is still an
almost-prime theorem, not the original prime-pair conjecture. -/
namespace Erdos972SuccessorRootAlmostPrime

open Finset
open Erdos972PrimePowerError Erdos972PrimeAlmostPrime
open Erdos972EfficientSieveScale Erdos972EfficientPrimeAlmostPrime
open Erdos972GrowingCoprimeCandidates

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 24577
attribute [local irreducible] fastRoot

/-- Roughness gives a lower bound of `Z+1`, rather than merely `Z`, for
every prime factor, including repeated factors. -/
lemma factor_length_of_successor_bound {q Z K : ℕ} (hq : 0 < q)
    (hc : q.Coprime Z.factorial) (hsize : q < (Z+1)^(K+1)) :
    q.primeFactorsList.length ≤ K := by
  have hfac : ∀ r ∈ q.primeFactorsList, Z+1 ≤ r := by
    intro r hr
    have hp := Nat.prime_of_mem_primeFactorsList hr
    have hrd := Nat.dvd_of_mem_primeFactorsList hr
    by_contra hh
    have hrf : r ∣ Z.factorial := hp.dvd_factorial.mpr (by omega)
    exact hp.ne_one (Nat.eq_one_of_dvd_coprimes hc hrd hrf)
  have hlower := List.pow_card_le_prod q.primeFactorsList (Z+1) hfac
  rw [Nat.prod_primeFactorsList hq.ne'] at hlower
  by_contra hh
  have hlen : K+1 ≤ q.primeFactorsList.length := by omega
  have hpow := Nat.pow_le_pow_right (show 1 ≤ Z+1 by omega) hlen
  exact (not_le_of_gt hsize) (hpow.trans hlower)

lemma fastRoot_successor_upper (u : ℕ) : u < (fastRoot u+1)^4096 := by
  apply Nat.lt_of_not_ge
  intro h
  have hh := (le_fastRoot_iff (fastRoot u+1) u).mpr h
  omega

/-- This avoids replacing `(Z+1)^4096` by the much larger `Z^8192`. -/
lemma floor_output_successor_bound {α : ℝ} {p u : ℕ}
    (hα : α ≤ fastRoot u) (hp : p ≤ u^6) :
    floorMul α p < (fastRoot u+1)^24577 := by
  have hfloor : floorMul α p ≤ fastRoot u*p := by
    unfold floorMul
    have hh := Nat.floor_mono (mul_le_mul_of_nonneg_right hα (Nat.cast_nonneg (α := ℝ) p))
    simpa only [← Nat.cast_mul, Nat.floor_natCast] using hh
  have hscale : u^6 ≤ (fastRoot u+1)^24576 := by
    have hh := Nat.pow_le_pow_left (fastRoot_successor_upper u).le 6
    simpa only [← pow_mul, Nat.reduceMul] using hh
  calc
    floorMul α p ≤ fastRoot u*p := hfloor
    _ ≤ fastRoot u*(fastRoot u+1)^24576 := Nat.mul_le_mul_left _ (hp.trans hscale)
    _ < (fastRoot u+1)*(fastRoot u+1)^24576 :=
      Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self _) (Nat.pow_pos (Nat.succ_pos _))
    _ = (fastRoot u+1)^24577 := (pow_succ' _ 24576).symm

lemma rough_output_factor_bound {α : ℝ} (hα : 1 ≤ α) {p u : ℕ}
    (hp : p.Prime) (hpN : p ≤ u^6) (hαZ : α ≤ fastRoot u)
    (hc : (floorMul α p).Coprime (fastRoot u).factorial) :
    (floorMul α p).primeFactorsList.length ≤ 24576 := by
  exact factor_length_of_successor_bound (floorMul_pos hα hp.pos) hc
    (floor_output_successor_bound hαZ hpN)

noncomputable def almostPrimeInputs (α : ℝ) (N : ℕ) : Finset ℕ := by
  classical
  exact (Ioc 0 N).filter (fun p => p.Prime ∧
    (floorMul α p).primeFactorsList.length ≤ 24576)

/-- The existing logarithmic-order rough-output count now supplies the
same quantitative lower bound with at most 24576 output factors. -/
theorem exists_prime_almostPrime_card_scale {α : ℝ} (hα : 1 < α)
    (hI : Irrational α) (B : ℕ) :
    ∃ u : ℕ, B < u ∧
      (u:ℝ)^6/(6*roughConstant*(1+Real.log (u+1:ℕ))^2) ≤
        (almostPrimeInputs α (u^6)).card := by
  classical
  obtain ⟨u, hu, hZ, hcount⟩ := exists_prime_rough_card_scale hα hI (max B ⌈α⌉₊)
  have hαZ : α ≤ fastRoot u := (Nat.le_ceil α).trans
    (Nat.cast_le.mpr ((le_max_right B _).trans hZ.le))
  refine ⟨u, (le_max_left B _).trans_lt hu, hcount.trans ?_⟩
  apply Nat.cast_le.mpr
  apply card_le_card
  intro p hp
  obtain ⟨hpI, hprime, hc⟩ := mem_filter.mp hp
  exact mem_filter.mpr ⟨hpI, hprime,
    rough_output_factor_bound hα.le hprime (mem_Ioc.mp hpI).2 hαZ hc⟩

/-- A scale-free form of the logarithmic-order counting lower bound. -/
theorem frequently_many_prime_almostPrime_pairs {α : ℝ}
    (hα : 1 < α) (hI : Irrational α) :
    ∃ c : ℝ, 0 < c ∧ ∀ B : ℕ, ∃ N : ℕ, B < N ∧
      c*N/(1+Real.log (N+1:ℕ))^2 ≤ (almostPrimeInputs α N).card := by
  let D : ℝ := 6*roughConstant
  have hD : 0 < D := mul_pos (by norm_num) roughConstant_pos
  refine ⟨1/D, by positivity, ?_⟩
  intro B
  obtain ⟨u, hu, hcount⟩ := exists_prime_almostPrime_card_scale hα hI B
  have hu1 : 1 ≤ u := (Nat.zero_le B).trans_lt hu
  have hun : u ≤ u^6 := by
    simpa only [pow_one] using Nat.pow_le_pow_right hu1 (show 1 ≤ 6 by decide)
  refine ⟨u^6, hu.trans_le hun, ?_⟩
  have hL : 0 < 1+Real.log (u+1:ℕ) := by linarith only [Real.log_natCast_nonneg (u+1)]
  have hlog : 1+Real.log (u+1:ℕ) ≤ 1+Real.log (u^6+1:ℕ) :=
    add_le_add_right (Erdos972ExponentialSum.monotone_log_natCast (Nat.add_le_add_right hun 1)) 1
  have hpow := pow_le_pow_left₀ hL.le hlog 2
  have hden := mul_le_mul_of_nonneg_left hpow hD.le
  have hmono := div_le_div_of_nonneg_left (show 0 ≤ (u:ℝ)^6 by positivity)
    (show 0 < D*(1+Real.log (u+1:ℕ))^2 by positivity) hden
  change (u:ℝ)^6/(D*(1+Real.log (u+1:ℕ))^2) ≤ _ at hcount
  have hh := hmono.trans hcount
  simpa only [Nat.cast_pow, one_div, div_eq_mul_inv, mul_inv_rev, mul_comm,
    mul_left_comm, mul_assoc, one_mul] using hh

/-- Prime inputs exceeding every threshold, with the sharper bounded
number of output factors. Primality of the output is NOT asserted. -/
theorem exists_prime_almostPrime_beyond {α : ℝ} (hα : 1 < α) (hI : Irrational α)
    (B : ℕ) : ∃ p : ℕ, B < p ∧ p.Prime ∧
      (floorMul α p).primeFactorsList.length ≤ 24576 := by
  let T := max ⌈14*roughConstant*(B:ℝ)⌉₊ ⌈α⌉₊
  obtain ⟨u, hu, hZ, hweight⟩ := exists_prime_rough_log_scale hα hI T
  have hu1 : 1 ≤ u := (Nat.zero_le T).trans_lt hu
  have hlargeU : 14*roughConstant*(B:ℝ) < u :=
    (Nat.le_ceil _).trans_lt (Nat.cast_lt.mpr ((le_max_left _ _).trans_lt hu))
  have hweightLarge : 7*(B:ℝ) < coprimePrimeWeight α (fastRoot u).factorial (u^6) :=
    (seven_mul_lt_div roughConstant_pos hlargeU).trans_le
      ((linear_below_log_weight roughConstant_pos hu1).trans hweight)
  obtain ⟨p, hpB, hpN, hp, hpc⟩ := prime_beyond_of_coprime_weight hweightLarge
  have hαZ : α ≤ fastRoot u := (Nat.le_ceil α).trans
    (Nat.cast_le.mpr ((le_max_right _ _).trans hZ.le))
  exact ⟨p, hpB, hp, rough_output_factor_bound hα.le hp hpN hαZ hpc⟩

theorem infinite_prime_almostPrime_inputs {α : ℝ} (hα : 1 < α) (hI : Irrational α) :
    {p : ℕ | p.Prime ∧ (floorMul α p).primeFactorsList.length ≤ 24576}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro B
  obtain ⟨p, hpB, hp, hΩ⟩ := exists_prime_almostPrime_beyond hα hI B
  exact ⟨p, ⟨hp, hΩ⟩, hpB⟩

#print axioms factor_length_of_successor_bound
#print axioms exists_prime_almostPrime_card_scale
#print axioms infinite_prime_almostPrime_inputs
#print axioms frequently_many_prime_almostPrime_pairs

end Erdos972SuccessorRootAlmostPrime
