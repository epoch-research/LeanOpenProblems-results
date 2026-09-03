import Submission.CappedLowerSieve
import Submission.PrimeAlmostPrime

/-! At arbitrarily large good scales the genuine prime-input / rough-output
weight has the expected logarithmic order, with a fixed (very small) positive
constant. The output still has only boundedly many prime factors, rather than
being certified prime. -/
namespace Erdos972PrimeRoughLogLower

open Finset Filter ArithmeticFunction
open scoped Topology
open Erdos972SelbergWeights Erdos972SelbergLowerMain Erdos972SelbergLowerTest
open Erdos972GrowingCoprimeCandidates Erdos972PrimePowerError
open Erdos972DualPrimeRows Erdos972ScaledPrimeRows Erdos972PolynomialRowScales
open Erdos972PrimeRotation Erdos972InverseGoodApproximation
open Erdos972PrimeRoughOutputs Erdos972PrimeAlmostPrime
open Erdos972SelbergMajorantSize Erdos972CappedLowerSieve

set_option maxHeartbeats 5000000
set_option exponentiation.threshold 8192

/-- A fixed positive constant, not a scale-dependent loss. -/
noncomputable def roughConstant : ℝ := 24*majorantCap 6291457

lemma roughConstant_pos : 0 < roughConstant :=
  mul_pos (by norm_num) (majorantCap_pos _)

theorem exists_prime_rough_log_scale {α : ℝ} (hα : 1 < α) (hI : Irrational α) (B : ℕ) :
    ∃ u : ℕ, B < u ∧ B < roughRoot u ∧
      (u:ℝ)^6/(roughConstant*(1+Real.log (u+1:ℕ))) ≤
        coprimePrimeWeight α (roughRoot u).factorial (u^6) := by
  have hlog := (Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop.comp roughRoot_tendsto)).eventually_ge_atTop 1
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (eventually_rough_prime_budget.and ((root64_tendsto.eventually_ge_atTop 2048).and
      (hlog.and (roughRoot_tendsto.eventually_gt_atTop (max B (max 2 ⌈α⌉₊))))))
  let A := max T (B+1)
  obtain ⟨r, hr, hden⟩ := Erdos972RationalRoute.exists_good_approximant_large_den hα hI (A^4)
  let u := Nat.sqrt (Nat.sqrt r.den)
  have hAu : A ≤ u := (le_fourth_root_iff A r.den).mpr hden.le
  have hTu : T ≤ u := (le_max_left T (B+1)).trans hAu
  have hBu : B < u := by have := (le_max_right T (B+1)).trans hAu; omega
  obtain ⟨hu, hlo, hhi⟩ := fourth_root_bounds r.pos
  change 0 < u at hu
  change u^4 ≤ r.den at hlo
  change r.den ≤ 16*u^4 at hhi
  clear_value u
  obtain ⟨⟨hψ, hbudget⟩, hv, hlogZ, hZbig⟩ := hT u hTu
  obtain ⟨hZ, helig⟩ := sieveRoot_eligible hu
  have hBZ : B < roughRoot u := (le_max_left B _).trans_lt hZbig
  have hZ2 : 2 ≤ roughRoot u := by
    exact (le_max_left 2 _).trans ((le_max_right B _).trans hZbig.le)
  have hαZ : α ≤ roughRoot u := (Nat.le_ceil α).trans
    (Nat.cast_le.mpr ((le_max_right 2 _).trans ((le_max_right B _).trans hZbig.le)))
  let Z := roughRoot u
  let R := Z^1024
  have hR : 1 ≤ R := Nat.one_le_pow 1024 Z hZ
  have hmod : R^2*Z ≤ root64 u := by
    apply le_trans _ helig
    exact Nat.mul_le_mul_right Z (Nat.pow_le_pow_right hR (by decide : 2 ≤ 5))
  have helig3 : R^3*Z ≤ root64 u := by
    apply le_trans _ helig
    exact Nat.mul_le_mul_right Z (Nat.pow_le_pow_right hR (by decide : 3 ≤ 5))
  have hE : 0 ≤ scaledRowError 1 u (root64 u)+
      (Chebyshev.psi (u^6 : ℕ)-Chebyshev.theta (u^6 : ℕ)) := by
    exact add_nonneg (scaledRowError_nonneg 1 u (root64 u))
      (sub_nonneg.mpr (Chebyshev.theta_le_psi _))
  have hcap : ∀ n ∈ Ioc 0 (u^6), (floorMul α n).Coprime Z.factorial →
      Erdos972PairSieve.majorant R (floorMul α n) ≤ majorantCap 6291457 := by
    intro n hn hc
    obtain ⟨hn0, hnN⟩ := mem_Ioc.mp hn
    have hfpos : 0 < floorMul α n := by
      apply Nat.floor_pos.mpr
      have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn0
      calc
        (1:ℝ) = 1*1 := by norm_num
        _ ≤ α*n := mul_le_mul hα.le hnR (by norm_num) (by linarith only [hα])
    apply majorant_bounded_factors hR hfpos.ne'
    exact factor_length_bound hfpos hZ2 hc
      (floor_output_power_bound hαZ hZ2 hnN)
  have hlower := rough_weight_log_lower (Ioc 0 (u^6)) primeWeight (floorMul α)
    (fun n _ => primeWeight_nonneg n) hR hZ helig3 hE (majorantCap_pos _) hψ
    (lowerMain_power_positive hZ hlogZ) hbudget hcap
    (fun d hd hdR => prime_row_discrepancy α d (u^6) (input_divisor_row_discrepancy
      (show 0 ≤ α by linarith) r hr.le (K := 1) (by norm_num) (by simpa using hv)
      (root64_bounds hu).2.1 (by simpa using hlo) (by simpa using hhi)
      hd (hdR.trans hmod) le_rfl))
  rw [rough_prime_sum] at hlower
  have hR5 : R^5 ≤ root64 u := (Nat.le_mul_of_pos_right _ hZ).trans helig
  clear_value R
  have hRR5 : R ≤ R^5 := by
    simpa only [pow_one] using Nat.pow_le_pow_right hR (show 1 ≤ 5 by decide)
  have hvu : root64 u ≤ u := by
    have hh : root64 u ≤ (root64 u)^64 := by
      simpa only [pow_one] using Nat.pow_le_pow_right (root64_bounds hu).1 (show 1 ≤ 64 by decide)
    exact hh.trans (root64_bounds hu).2.1
  have hRu : R ≤ u := hRR5.trans (hR5.trans hvu)
  refine ⟨u, hBu, hBZ, ?_⟩
  apply le_trans _ hlower
  rw [Nat.cast_pow]
  have hC := majorantCap_pos 6291457
  have hL : 0 < 1+Real.log (R+1:ℕ) := by linarith only [Real.log_natCast_nonneg (R+1)]
  have h24C : 0 < 24*majorantCap 6291457 := mul_pos (by norm_num) hC
  change (u:ℝ)^6/(24*majorantCap 6291457*(1+Real.log (u+1:ℕ))) ≤ _
  apply div_le_div_of_nonneg_left (by positivity) (mul_pos h24C hL)
  exact mul_le_mul_of_nonneg_left (add_le_add_right
    (Erdos972ExponentialSum.monotone_log_natCast (Nat.add_le_add_right hRu 1)) 1)
    h24C.le

noncomputable def roughInputs (α : ℝ) (Z N : ℕ) : Finset ℕ := by
  classical
  exact (Ioc 0 N).filter (fun p => p.Prime ∧ (floorMul α p).Coprime Z.factorial)

noncomputable def almostPrimeInputs (α : ℝ) (N : ℕ) : Finset ℕ := by
  classical
  exact (Ioc 0 N).filter (fun p => p.Prime ∧
    (floorMul α p).primeFactorsList.length ≤ 6291457)

lemma coprimePrimeWeight_card_upper (α : ℝ) (Z : ℕ) {u : ℕ} (_hu : 0 < u) :
    coprimePrimeWeight α Z.factorial (u^6) ≤
      6*(1+Real.log (u+1:ℕ))*(roughInputs α Z (u^6)).card := by
  classical
  change (∑ p ∈ roughInputs α Z (u^6), Real.log p) ≤ _
  have hs : (∑ p ∈ roughInputs α Z (u^6), Real.log p) ≤
      ∑ p ∈ roughInputs α Z (u^6), 6*(1+Real.log (u+1:ℕ)) := by
    apply sum_le_sum
    intro p hp
    obtain ⟨hpI, _⟩ := mem_filter.mp hp
    have hlog := Erdos972ExponentialSum.monotone_log_natCast (mem_Ioc.mp hpI).2
    change Real.log p ≤ Real.log (u^6:ℕ) at hlog
    rw [Nat.cast_pow, Real.log_pow] at hlog
    have hnext := Erdos972ExponentialSum.monotone_log_natCast (Nat.le_succ u)
    norm_num only [Nat.cast_ofNat] at hlog
    linarith only [hlog, hnext]
  simpa only [sum_const, nsmul_eq_mul, mul_comm] using hs

lemma logarithmic_count_transfer {C L X A : ℝ} (hC : 0 < C) (hL : 0 < L)
    (h : X/(C*L) ≤ 6*L*A) : X/(6*C*L^2) ≤ A := by
  apply (div_le_iff₀ (show 0 < 6*C*L^2 by positivity)).mpr
  have hh := (div_le_iff₀ (mul_pos hC hL)).mp h
  nlinarith only [hh]

theorem exists_prime_rough_card_scale {α : ℝ} (hα : 1 < α) (hI : Irrational α) (B : ℕ) :
    ∃ u : ℕ, B < u ∧ B < roughRoot u ∧
      (u:ℝ)^6/(6*roughConstant*(1+Real.log (u+1:ℕ))^2) ≤
        (roughInputs α (roughRoot u) (u^6)).card := by
  obtain ⟨u, hu, hZ, hweight⟩ := exists_prime_rough_log_scale hα hI B
  have hu0 : 0 < u := (Nat.zero_le B).trans_lt hu
  refine ⟨u, hu, hZ, logarithmic_count_transfer roughConstant_pos ?_
    (hweight.trans (coprimePrimeWeight_card_upper α (roughRoot u) hu0))⟩
  linarith only [Real.log_natCast_nonneg (u+1)]

/-- A genuine counting lower bound of logarithmic order at arbitrarily large
scales. The bound on the number of output factors is still 6291457, NOT one. -/
theorem exists_prime_almostPrime_card_scale {α : ℝ} (hα : 1 < α) (hI : Irrational α)
    (B : ℕ) : ∃ u : ℕ, B < u ∧
      (u:ℝ)^6/(6*roughConstant*(1+Real.log (u+1:ℕ))^2) ≤
        (almostPrimeInputs α (u^6)).card := by
  classical
  let B' := max B (max 2 ⌈α⌉₊)
  obtain ⟨u, hu, hZ, hcount⟩ := exists_prime_rough_card_scale hα hI B'
  have hZ2 : 2 ≤ roughRoot u := (le_max_left 2 _).trans ((le_max_right B _).trans hZ.le)
  have hαZ : α ≤ roughRoot u := (Nat.le_ceil α).trans
    (Nat.cast_le.mpr ((le_max_right 2 _).trans ((le_max_right B _).trans hZ.le)))
  refine ⟨u, (le_max_left B _).trans_lt hu, hcount.trans ?_⟩
  apply Nat.cast_le.mpr
  apply card_le_card
  intro p hp
  obtain ⟨hpI, hprime, hc⟩ := mem_filter.mp hp
  apply mem_filter.mpr
  refine ⟨hpI, hprime, ?_⟩
  have hfpos : 0 < floorMul α p := by
    apply Nat.floor_pos.mpr
    have hnR : (1:ℝ) ≤ p := by exact_mod_cast hprime.one_le
    calc
      (1:ℝ) = 1*1 := by norm_num
      _ ≤ α*p := mul_le_mul hα.le hnR (by norm_num) (by linarith only [hα])
  exact factor_length_bound hfpos hZ2 hc
    (floor_output_power_bound hαZ hZ2 (mem_Ioc.mp hpI).2)

/-- A scale-free formulation of the quantitative almost-prime result.
It does not replace the output factor bound by primality. -/
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

#print axioms frequently_many_prime_almostPrime_pairs
#print axioms exists_prime_rough_log_scale
#print axioms exists_prime_rough_card_scale
#print axioms exists_prime_almostPrime_card_scale

end Erdos972PrimeRoughLogLower
