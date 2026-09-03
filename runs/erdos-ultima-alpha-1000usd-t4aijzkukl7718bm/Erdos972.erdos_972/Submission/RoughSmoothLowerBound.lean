import Submission.EfficientPrimeAlmostPrime
import Submission.PrimeLeastFactorScales

/-!
A genuine lower bound for the mixed prime--smooth sum, obtained from the
already established rough-output lower sieve. This is not a lower bound
for the genuine prime-pair sum: the smoothing comparison error is larger.
-/
namespace Erdos972RoughSmoothLowerBound

open Finset Filter ArithmeticFunction
open scoped Topology
open Erdos972SmoothMangoldt Erdos972SmoothMangoldtPositive
open Erdos972SharpSmoothMangoldt Erdos972PrimePowerError
open Erdos972PrimeRoughOutputs Erdos972GrowingCoprimeCandidates
open Erdos972PrimeAlmostPrime Erdos972EfficientSieveScale
open Erdos972PrimeLeastFactorScales Erdos972LeastFactorCutoff

set_option maxHeartbeats 2000000
set_option exponentiation.threshold 8192

lemma exp_factor_lower {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1/2) :
    x/2 ≤ 1-Real.exp (-x) := by
  have he := exp_slope_error (t := 1) (x := x) (by norm_num) hx
  norm_num only [one_mul, div_one, neg_one_mul] at he
  have hl := (abs_le.mp he).1
  nlinarith

lemma primeFactor_gt_of_coprime_factorial {n Z p : ℕ}
    (hc : n.Coprime Z.factorial) (hp : p ∈ n.primeFactors) : Z < p := by
  have hprime := Nat.prime_of_mem_primeFactors hp
  by_contra h
  exact hprime.ne_one (Nat.eq_one_of_dvd_coprimes hc
    (Nat.dvd_of_mem_primeFactors hp) (hprime.dvd_factorial.mpr (by omega)))

/-- A pointwise lower bound on a rough output with boundedly many factors.
The exponent is an almost-prime factor bound, not a prime assertion. -/
theorem rough_smooth_lower {t : ℝ} (ht : 0 < t) {n Z K : ℕ}
    (hn : 1 < n) (hZ : 1 < Z) (hc : n.Coprime Z.factorial)
    (hK : n.primeFactorsList.length ≤ K) (hsmall : t*Real.log Z ≤ 1/2) :
    (t*Real.log Z/2)^K/t ≤ smoothMangoldt t n := by
  have hlog0 : 0 ≤ Real.log Z := Real.log_natCast_nonneg Z
  have hx : 0 ≤ t*Real.log Z := mul_nonneg ht.le hlog0
  have hb0 : 0 ≤ t*Real.log Z/2 := by positivity
  have hb1 : t*Real.log Z/2 ≤ 1 := by linarith
  have hcard : n.primeFactors.card ≤ K :=
    (List.toFinset_card_le n.primeFactorsList).trans hK
  have he : (t*Real.log Z/2)^K ≤ expDivisorSum t n := by
    rw [expDivisorSum_product t (by omega)]
    calc
      _ ≤ (t*Real.log Z/2)^n.primeFactors.card :=
        pow_le_pow_of_le_one hb0 hb1 hcard
      _ = ∏ p ∈ n.primeFactors, (t*Real.log Z/2) := (prod_const _).symm
      _ ≤ _ := by
        apply prod_le_prod (fun _ _ => hb0)
        intro p hp
        apply (exp_factor_lower hx hsmall).trans
        have hl := Real.log_le_log (Nat.cast_pos.mpr (by omega : 0 < Z))
          (Nat.cast_le.mpr (primeFactor_gt_of_coprime_factorial hc hp).le)
        have hh := Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hl (by linarith : -t ≤ 0))
        simpa only [neg_mul] using sub_le_sub_left hh 1
  rw [smoothMangoldt, expDivisorSum_at_zero, one_apply, if_neg (by omega : n ≠ 1), sub_zero]
  exact div_le_div_of_nonneg_right he ht.le

/-- Restricting the mixed sum to certified rough outputs gives a finite,
unconditional smoothed lower bound. -/
theorem mixed_lower_from_rough {α t : ℝ} (hα : 1 ≤ α) (ht : 0 < t)
    {N Z K : ℕ} (hZ : 1 < Z) (hsmall : t*Real.log Z ≤ 1/2)
    (hsize : ∀ p ∈ Ioc 0 N, floorMul α p ≤ Z^K) :
    (t*Real.log Z/2)^K/t * coprimePrimeWeight α Z.factorial N ≤
      mixedPrimeSmooth t α N := by
  classical
  rw [coprimePrimeWeight, mul_sum]
  calc
    _ ≤ ∑ p ∈ (Ioc 0 N).filter
        (fun p => p.Prime ∧ (floorMul α p).Coprime Z.factorial),
        primeWeight p*smoothMangoldt t (floorMul α p) := by
      apply sum_le_sum
      intro p hp
      obtain ⟨hpN, hpp, hpc⟩ := mem_filter.mp hp
      have hpout : 1 < floorMul α p := by
        have hh : p ≤ floorMul α p := by
          unfold floorMul
          exact Nat.le_floor (by simpa using
            mul_le_mul_of_nonneg_right hα (Nat.cast_nonneg (α := ℝ) p))
        exact (show 1 < p from hpp.two_le).trans_le hh
      have hk := factor_length_bound (by omega : 0 < floorMul α p) hZ hpc (hsize p hpN)
      have hl := rough_smooth_lower ht hpout hZ hpc hk hsmall
      rw [primeWeight, if_pos hpp]
      exact (by simpa only [mul_comm] using
        mul_le_mul_of_nonneg_left hl (Real.log_natCast_nonneg p))
    _ ≤ mixedPrimeSmooth t α N := by
      apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      intro p hp _
      exact mul_nonneg (primeWeight_nonneg p) (smoothMangoldt_nonneg ht _)

lemma fastRoot_log_comparison {u : ℕ} (hZ : 2 ≤ fastRoot u) :
    1+Real.log (u+1:ℕ) ≤ 8195*Real.log (fastRoot u) := by
  have hZu : fastRoot u ≤ u :=
    (root64_le_self (Erdos972PolynomialRowScales.root64 u)).trans (root64_le_self u)
  have hu : 0 < u := by omega
  have hzpos : (0:ℝ) < fastRoot u := Nat.cast_pos.mpr (by omega)
  have hlog := Erdos972ExponentialSum.monotone_log_natCast (fastRoot_upper hZ)
  dsimp only at hlog
  rw [Nat.cast_pow, Real.log_pow] at hlog
  have hinc := Erdos972ExponentialSum.monotone_log_natCast
    (show u+1 ≤ 2*u by omega)
  dsimp only at hinc
  rw [Nat.cast_mul, Nat.cast_ofNat,
    Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (Nat.cast_ne_zero.mpr hu.ne')] at hinc
  have htwo : Real.log 2 ≤ Real.log (fastRoot u) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hZ)
  have hzhalf : (1/2:ℝ) ≤ Real.log (fastRoot u) := by
    linarith only [Real.log_two_gt_d9, htwo]
  norm_num only [Nat.cast_ofNat] at hlog
  linarith only [hlog, hinc, htwo, hzhalf]

lemma weighted_log_lower_transfer {A z τ C L X Y S : ℝ}
    (hA : 0 ≤ A) (hz : 0 < z) (hτ : 0 < τ) (hC : 0 < C) (hL : 0 < L)
    (hX : 0 ≤ X) (hzL : L ≤ 8195*z)
    (hweight : X/(C*L) ≤ Y) (hS : A/(τ/z)*Y ≤ S) :
    A/(8195*τ*C)*X ≤ S := by
  have hr : (1/8195:ℝ) ≤ z/L := (le_div_iff₀ hL).mpr (by linarith only [hzL])
  calc
    _ = ((A/τ)*(X/C))*(1/8195) := by ring
    _ ≤ ((A/τ)*(X/C))*(z/L) := mul_le_mul_of_nonneg_left hr (by positivity)
    _ = A/(τ/z)*(X/(C*L)) := by field_simp
    _ ≤ A/(τ/z)*Y := mul_le_mul_of_nonneg_left hweight (by positivity)
    _ ≤ S := hS

noncomputable def roughParameter (τ : ℝ) (u : ℕ) : ℝ :=
  τ/Real.log (fastRoot u)

noncomputable def roughSmoothCoefficient (τ : ℝ) : ℝ :=
  (τ/2)^49153/(8195*τ*Erdos972EfficientPrimeAlmostPrime.roughConstant)

lemma roughSmoothCoefficient_pos {τ : ℝ} (hτ : 0 < τ) :
    0 < roughSmoothCoefficient τ := by
  unfold roughSmoothCoefficient
  exact div_pos (pow_pos (by positivity) _)
    (mul_pos (mul_pos (by norm_num) hτ) Erdos972EfficientPrimeAlmostPrime.roughConstant_pos)

/-- An actual lower bound on a family of joint smoothing parameters.
The scale is selected first; the conclusion holds for every admissible `τ`
at that same scale. It does not assert a lower bound on prime pairs. -/
theorem exists_rough_smooth_scale {α : ℝ} (hα : 1 < α) (hI : Irrational α) (B : ℕ) :
    ∃ u : ℕ, B < u ∧ 2 ≤ fastRoot u ∧ α ≤ fastRoot u ∧
      ∀ τ : ℝ, 0 < τ → τ ≤ 1/2 →
        roughSmoothCoefficient τ*(u:ℝ)^6 ≤ mixedPrimeSmooth (roughParameter τ u) α (u^6) := by
  let B' := max B (max 2 ⌈α⌉₊)
  obtain ⟨u, hu, hZ, hweight⟩ :=
    Erdos972EfficientPrimeAlmostPrime.exists_prime_rough_log_scale hα hI B'
  have hZ2 : 2 ≤ fastRoot u :=
    (le_max_left 2 _).trans ((le_max_right B _).trans hZ.le)
  have hαZ : α ≤ fastRoot u := (Nat.le_ceil α).trans
    (Nat.cast_le.mpr ((le_max_right 2 _).trans ((le_max_right B _).trans hZ.le)))
  refine ⟨u, (le_max_left B _).trans_lt hu, hZ2, hαZ, ?_⟩
  intro τ hτ hτsmall
  have hlog : 0 < Real.log (fastRoot u) := Real.log_pos (by exact_mod_cast hZ2)
  have ht : 0 < roughParameter τ u := div_pos hτ hlog
  have he : roughParameter τ u*Real.log (fastRoot u) = τ :=
    div_mul_cancel₀ τ hlog.ne'
  have hs := mixed_lower_from_rough hα.le ht (show 1 < fastRoot u from hZ2)
    (by rw [he]; exact hτsmall)
    (K := 49153) (N := u^6)
    (fun p hp => fast_floor_output_power_bound hαZ hZ2 (mem_Ioc.mp hp).2)
  rw [he] at hs
  have hLpos : 0 < 1+Real.log (u+1:ℕ) := by
    linarith only [Real.log_natCast_nonneg (u+1)]
  have hXpos : 0 ≤ (u:ℝ)^6 := pow_nonneg (Nat.cast_nonneg u) _
  have hbase := weighted_log_lower_transfer (A := (τ/2)^49153)
    (z := Real.log (fastRoot u)) (τ := τ)
    (C := Erdos972EfficientPrimeAlmostPrime.roughConstant)
    (L := 1+Real.log (u+1:ℕ)) (X := (u:ℝ)^6)
    (Y := coprimePrimeWeight α (fastRoot u).factorial (u^6))
    (pow_nonneg (div_nonneg hτ.le (by norm_num)) _) hlog hτ
    Erdos972EfficientPrimeAlmostPrime.roughConstant_pos hLpos hXpos
    (fastRoot_log_comparison hZ2) hweight hs
  exact hbase

#print axioms rough_smooth_lower
#print axioms mixed_lower_from_rough
#print axioms exists_rough_smooth_scale

end Erdos972RoughSmoothLowerBound
