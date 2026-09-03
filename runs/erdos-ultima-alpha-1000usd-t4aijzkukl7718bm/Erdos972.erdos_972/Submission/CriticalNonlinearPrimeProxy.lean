import Submission.NonlinearPrimeProxy
import Submission.PrimePairKernelSummability

/-! At the critical parameter two, the nonlinear prime proxy still has
summable composite error. This supplies no prime-input lower bound. -/
namespace Erdos972CriticalNonlinearPrimeProxy

open Finset Filter ArithmeticFunction
open scoped Topology
open Erdos972SmoothMangoldt Erdos972SmoothMangoldtPositive Erdos972PrimePowerError
open Erdos972NonlinearPrimeProxy Erdos972PrimePairKernelSummability

set_option autoImplicit false
set_option maxHeartbeats 2000000

lemma exp_neg_two_log {n : ℕ} (hn : 0 < n) :
    Real.exp (-(2:ℝ)*Real.log n) = ((n:ℝ)^2)⁻¹ := by
  rw [neg_mul, Real.exp_neg, show (2:ℝ)*Real.log n = Real.log ((n:ℝ)^2) by
    rw [Real.log_pow]; norm_num,
    Real.exp_log (sq_pos_of_pos (Nat.cast_pos.mpr hn))]

/-- Retain the least-factor cofactor rather than replacing it by sqrt(n). -/
lemma primeProxy_two_le_cofactor {n : ℕ} (hn : 1 < n) :
    primeProxy 2 n ≤ (((n/n.minFac:ℕ):ℝ)^2)⁻¹ := by
  let p : ℕ := n.minFac
  let m : ℕ := n/p
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hnfac : n = p*m := (Nat.mul_div_cancel' (Nat.minFac_dvd n)).symm
  have hm : 0 < m := by
    by_contra h
    have hm0 : m = 0 := Nat.eq_zero_of_not_pos h
    rw [hm0, mul_zero] at hnfac
    omega
  have hlog : Real.log n = Real.log p+Real.log m := by
    rw [hnfac, Nat.cast_mul, Real.log_mul (Nat.cast_ne_zero.mpr hp.ne_zero)
      (Nat.cast_ne_zero.mpr hm.ne')]
  have hd := euler_defect_ge_factor (by norm_num : (0:ℝ) ≤ 2) (by omega : n ≠ 0)
    (Nat.mem_primeFactors.mpr ⟨hp, Nat.minFac_dvd n, by omega⟩)
  rw [primeProxy, if_pos hn]
  calc
    _ ≤ Real.exp (-(2:ℝ)*Real.log n)/Real.exp (-(2:ℝ)*Real.log p) :=
      div_le_div_of_nonneg_left (Real.exp_nonneg _) (Real.exp_pos _) hd
    _ = Real.exp (-(2:ℝ)*Real.log m) := by
      rw [← Real.exp_sub, hlog]
      congr 1
      ring
    _ = _ := exp_neg_two_log hm

lemma minFac_cube_le_of_composite_cofactor {n : ℕ} (hn : 1 < n)
    (hnp : ¬ n.Prime) (hmnp : ¬ (n/n.minFac).Prime) : n.minFac^3 ≤ n := by
  let p : ℕ := n.minFac
  let m : ℕ := n/p
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hpm : p ≤ m := Nat.minFac_le_div (by omega) hnp
  have hm1 : 1 < m := hp.one_lt.trans_le hpm
  have hmp : m.minFac.Prime := Nat.minFac_prime (by omega)
  have hmdvd : m ∣ n := Nat.div_dvd_of_dvd (Nat.minFac_dvd n)
  have hpmin : p ≤ m.minFac := Nat.minFac_le_of_dvd hmp.two_le
    ((Nat.minFac_dvd m).trans hmdvd)
  have hp2 : p^2 ≤ m := (Nat.pow_le_pow_left hpmin 2).trans
    (Nat.minFac_sq_le_self (by omega) hmnp)
  calc
    _ = p*p^2 := (pow_succ' p 2)
    _ ≤ p*m := Nat.mul_le_mul_left p hp2
    _ = n := Nat.mul_div_cancel' (Nat.minFac_dvd n)

/-- All composites except products of two primes have a power-summable
pointwise envelope at the critical parameter. -/
lemma primeProxy_two_three_factor_bound {n : ℕ} (hn : 1 < n)
    (hnp : ¬ n.Prime) (hmnp : ¬ (n/n.minFac).Prime) :
    primeProxy 2 n ≤ (n:ℝ)^(-(4/3:ℝ)) := by
  have hp := Nat.minFac_prime (by omega : n ≠ 1)
  have hn0 : (0:ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hcube := minFac_cube_le_of_composite_cofactor hn hnp hmnp
  have hlogs : 3*Real.log n.minFac ≤ Real.log n := by
    have hh := Real.log_le_log
      (show (0:ℝ) < (n.minFac^3:ℕ) by exact_mod_cast Nat.pow_pos hp.pos)
      (Nat.cast_le.mpr hcube)
    rw [Nat.cast_pow, Real.log_pow] at hh
    simpa only [Nat.cast_ofNat] using hh
  have hd := euler_defect_ge_factor (by norm_num : (0:ℝ) ≤ 2) (by omega : n ≠ 0)
    (Nat.mem_primeFactors.mpr ⟨hp, Nat.minFac_dvd n, by omega⟩)
  have hlow : Real.exp (-(2/3:ℝ)*Real.log n) ≤ 1-expDivisorSum 2 n := by
    apply le_trans _ hd
    apply Real.exp_le_exp.mpr
    linarith only [hlogs]
  rw [primeProxy, if_pos hn]
  calc
    _ ≤ Real.exp (-(2:ℝ)*Real.log n)/Real.exp (-(2/3:ℝ)*Real.log n) :=
      div_le_div_of_nonneg_left (Real.exp_nonneg _) (Real.exp_pos _) hlow
    _ = _ := by
      rw [← Real.exp_sub, Real.rpow_def_of_pos hn0]
      congr 1
      ring

def semiprimeInputs : Set ℕ :=
  {n | 1 < n ∧ ¬ n.Prime ∧ (n/n.minFac).Prime}

def factorPair (n : semiprimeInputs) : PrimeIndex × PrimeIndex :=
  (⟨n.val.minFac, Nat.minFac_prime (by have := n.property.1; omega)⟩,
    ⟨n.val/n.val.minFac, n.property.2.2⟩)

lemma factorPair_injective : Function.Injective factorPair := by
  intro x y h
  apply Subtype.ext
  have hh := congrArg (fun z : PrimeIndex × PrimeIndex => z.1.val*z.2.val) h
  change x.val.minFac*(x.val/x.val.minFac) = y.val.minFac*(y.val/y.val.minFac) at hh
  simpa only [Nat.mul_div_cancel' (Nat.minFac_dvd x.val),
    Nat.mul_div_cancel' (Nat.minFac_dvd y.val)] using hh

lemma primeProxy_two_le_pairKernel (n : semiprimeInputs) :
    primeProxy 2 n.val ≤ pairKernel (factorPair n) := by
  have hpm := Nat.minFac_le_div (show 0 < n.val by have := n.property.1; omega)
    n.property.2.1
  change primeProxy 2 n.val ≤ (((max n.val.minFac (n.val/n.val.minFac):ℕ):ℝ)^2)⁻¹
  rw [max_eq_right hpm]
  exact primeProxy_two_le_cofactor n.property.1

lemma summable_semiprime_proxy : Summable (fun n : semiprimeInputs => primeProxy 2 n.val) := by
  have hh := summable_pairKernel.comp_injective factorPair_injective
  exact hh.of_nonneg_of_le
    (fun n => primeProxy_nonneg (by norm_num : (0:ℝ) ≤ 2) n.val)
    primeProxy_two_le_pairKernel

noncomputable def compositeProxyTwo (n : ℕ) : ℝ := if n.Prime then 0 else primeProxy 2 n

lemma compositeProxyTwo_nonneg (n : ℕ) : 0 ≤ compositeProxyTwo n := by
  unfold compositeProxyTwo
  split_ifs
  · exact le_rfl
  · exact primeProxy_nonneg (by norm_num) n

/-- The complete composite contribution is summable over ALL natural
inputs at t=2. In particular, this does not need prime-input correlation
estimates, irrationality, or selected scales. -/
theorem summable_compositeProxyTwo : Summable compositeProxyTwo := by
  classical
  have hs : Summable (semiprimeInputs.indicator (fun n => primeProxy 2 n)) :=
    (summable_subtype_iff_indicator (f := fun n => primeProxy 2 n) (s := semiprimeInputs)).mp
      summable_semiprime_proxy
  have hr : Summable (fun n : ℕ => (n:ℝ)^(-(4/3:ℝ))) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  apply (hs.add hr).of_nonneg_of_le compositeProxyTwo_nonneg
  intro n
  have hpow0 : 0 ≤ (n:ℝ)^(-(4/3:ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hsf0 : 0 ≤ semiprimeInputs.indicator (fun n => primeProxy 2 n) n :=
    Set.indicator_nonneg (fun n _ => primeProxy_nonneg (by norm_num) n) n
  by_cases hnp : n.Prime
  · simpa only [compositeProxyTwo, if_pos hnp] using add_nonneg hsf0 hpow0
  · by_cases hn : 1 < n
    · by_cases hm : (n/n.minFac).Prime
      · have hmem : n ∈ semiprimeInputs := ⟨hn, hnp, hm⟩
        rw [compositeProxyTwo, if_neg hnp, Set.indicator_of_mem hmem]
        exact le_add_of_nonneg_right hpow0
      · have hnot : n ∉ semiprimeInputs := fun hh => hm hh.2.2
        rw [compositeProxyTwo, if_neg hnp, Set.indicator_of_notMem hnot, zero_add]
        exact primeProxy_two_three_factor_bound hn hnp hm
    · simpa only [compositeProxyTwo, if_neg hnp, primeProxy, if_neg hn]
        using add_nonneg hsf0 hpow0

noncomputable def primeProxyWeightTwo (α : ℝ) (n : ℕ) : ℝ :=
  if n.Prime then primeProxy 2 (floorMul α n) else 0

noncomputable def primeInputErrorTwo (α : ℝ) (n : ℕ) : ℝ :=
  primeProxyWeightTwo α n-primePairIndicator α n

lemma primeInputErrorTwo_bounds (α : ℝ) (n : ℕ) :
    0 ≤ primeInputErrorTwo α n ∧
      primeInputErrorTwo α n ≤ compositeProxyTwo (floorMul α n) := by
  classical
  by_cases hp : n.Prime
  · by_cases hq : (floorMul α n).Prime
    · simp [primeInputErrorTwo, primeProxyWeightTwo, primePairIndicator, compositeProxyTwo,
        hp, hq, primeProxy_prime (by norm_num : (0:ℝ) ≤ 2) hq]
    · simp only [primeInputErrorTwo, primeProxyWeightTwo, primePairIndicator, compositeProxyTwo,
        hp, hq, and_false, if_true, if_false, sub_zero]
      exact ⟨primeProxy_nonneg (by norm_num) _, le_rfl⟩
  · simpa only [primeInputErrorTwo, primeProxyWeightTwo, primePairIndicator,
      hp, false_and, if_false, sub_self] using
      And.intro (le_refl (0:ℝ)) (compositeProxyTwo_nonneg (floorMul α n))

theorem summable_primeInputErrorTwo {α : ℝ} (hα : 1 ≤ α) :
    Summable (primeInputErrorTwo α) := by
  have hh := summable_compositeProxyTwo.comp_injective (floorMul_strictMono hα).injective
  exact hh.of_nonneg_of_le (fun n => (primeInputErrorTwo_bounds α n).1)
    (fun n => (primeInputErrorTwo_bounds α n).2)

/-- A universal composite-error budget for every finite input set and
every slope alpha>=1. The constant does not depend on alpha or the cutoff. -/
theorem primeInputErrorTwo_sum_le {α : ℝ} (hα : 1 ≤ α) (S : Finset ℕ) :
    (∑ n ∈ S, primeInputErrorTwo α n) ≤ ∑' q : ℕ, compositeProxyTwo q := by
  classical
  calc
    _ ≤ ∑ n ∈ S, compositeProxyTwo (floorMul α n) :=
      sum_le_sum (fun n _ => (primeInputErrorTwo_bounds α n).2)
    _ = ∑ q ∈ S.image (floorMul α), compositeProxyTwo q := by
      rw [sum_image (floorMul_strictMono hα).injective.injOn]
    _ ≤ _ := summable_compositeProxyTwo.sum_le_tsum _
      (fun q _ => compositeProxyTwo_nonneg q)

/-- At t=2, the first J moments still capture at most J/p^2 of the value
one at a prime p. No uniform high-moment estimate is inferred. -/
theorem prime_truncated_proxy_bound_two {p : ℕ} (hp : p.Prime) (J : ℕ) :
    (∑ j ∈ range J, Real.exp (-(2:ℝ)*Real.log p)*(expDivisorSum 2 p)^j) ≤
      (J:ℝ)/(p:ℝ)^2 := by
  have he0 := expDivisorSum_nonneg (by norm_num : (0:ℝ) ≤ 2) p
  have he1 : expDivisorSum 2 p ≤ 1 := by
    linarith only [euler_defect_pos (by norm_num : (0:ℝ) ≤ 2) hp.one_lt]
  have hs : (∑ j ∈ range J, Real.exp (-(2:ℝ)*Real.log p)*(expDivisorSum 2 p)^j) ≤
      ∑ j ∈ range J, Real.exp (-(2:ℝ)*Real.log p) := by
    apply sum_le_sum
    intro j hj
    exact (mul_le_mul_of_nonneg_left (pow_le_one₀ he0 he1) (Real.exp_nonneg _)).trans_eq
      (mul_one _)
  simpa only [sum_const, card_range, nsmul_eq_mul, exp_neg_two_log hp.pos,
    div_eq_mul_inv] using hs

/-- Critical-parameter version of the exact summability criterion.
Nonsummability remains an UNPROVED arithmetic input for irrational slopes. -/
theorem summable_primeProxyWeightTwo_iff_finite {α : ℝ} (hα : 1 ≤ α) :
    Summable (primeProxyWeightTwo α) ↔
      {p : ℕ | p.Prime ∧ (floorMul α p).Prime}.Finite := by
  classical
  constructor
  · intro hs
    have hsmall := (tendsto_order.mp hs.tendsto_atTop_zero).2 1 zero_lt_one
    obtain ⟨B, hB⟩ := eventually_atTop.mp hsmall
    apply (Set.finite_Iio B).subset
    intro p hp
    change p < B
    by_contra hnot
    have hh := hB p (le_of_not_gt hnot)
    have hval : primeProxyWeightTwo α p = 1 := by
      simp only [primeProxyWeightTwo, if_pos hp.1,
        primeProxy_prime (by norm_num : (0:ℝ) ≤ 2) hp.2]
    rw [hval] at hh
    exact (lt_irrefl 1) hh
  · intro hfin
    have hi : Summable (primePairIndicator α) := by
      apply summable_of_ne_finset_zero (s := hfin.toFinset)
      intro p hp
      have hnot : ¬ (p.Prime ∧ (floorMul α p).Prime) := by
        simpa only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] using hp
      simp [primePairIndicator, hnot]
    apply (hi.add (summable_primeInputErrorTwo hα)).congr
    intro n
    unfold primeInputErrorTwo
    ring

#print axioms primeProxy_two_le_cofactor
#print axioms primeProxy_two_three_factor_bound
#print axioms summable_semiprime_proxy
#print axioms summable_compositeProxyTwo
#print axioms summable_primeInputErrorTwo
#print axioms summable_primeProxyWeightTwo_iff_finite
#print axioms primeInputErrorTwo_sum_le
#print axioms prime_truncated_proxy_bound_two

end Erdos972CriticalNonlinearPrimeProxy
