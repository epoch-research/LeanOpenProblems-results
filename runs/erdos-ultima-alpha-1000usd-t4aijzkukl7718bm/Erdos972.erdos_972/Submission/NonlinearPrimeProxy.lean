import Submission.SmoothMangoldtPositive

/-! A nonlinear fixed-parameter prime detector. Its composite error is
summable at parameter four. No lower bound for its prime-input sum is
asserted here. -/
namespace Erdos972NonlinearPrimeProxy

open Finset Filter ArithmeticFunction
open scoped Topology
open Erdos972SmoothMangoldt Erdos972SmoothMangoldtPositive Erdos972PrimePowerError

set_option autoImplicit false
set_option maxHeartbeats 1500000

noncomputable def primeProxy (t : ℝ) (n : ℕ) : ℝ :=
  if 1 < n then Real.exp (-t*Real.log n)/(1-expDivisorSum t n) else 0

lemma euler_defect_ge_factor {t : ℝ} (ht : 0 ≤ t) {n p : ℕ}
    (hn : n ≠ 0) (hp : p ∈ n.primeFactors) :
    Real.exp (-t*Real.log p) ≤ 1-expDivisorSum t n := by
  rw [expDivisorSum_product t hn]
  rw [← prod_erase_mul n.primeFactors (fun q : ℕ => 1-Real.exp (-t*Real.log q)) hp]
  have hrest : (∏ q ∈ n.primeFactors.erase p, (1-Real.exp (-t*Real.log q))) ≤ 1 :=
    prod_le_one (fun q _ => expFactor_nonneg ht q) (fun q _ => expFactor_le_one t q)
  have hh := mul_le_mul_of_nonneg_right hrest (expFactor_nonneg ht p)
  nlinarith only [hh]

lemma euler_defect_pos {t : ℝ} (ht : 0 ≤ t) {n : ℕ} (hn : 1 < n) :
    0 < 1-expDivisorSum t n := by
  have hp := Nat.minFac_prime (by omega : n ≠ 1)
  exact (Real.exp_pos (-t*Real.log n.minFac)).trans_le
    (euler_defect_ge_factor ht (by omega) (Nat.mem_primeFactors.mpr
      ⟨hp, Nat.minFac_dvd n, by omega⟩))

lemma primeProxy_nonneg {t : ℝ} (ht : 0 ≤ t) (n : ℕ) : 0 ≤ primeProxy t n := by
  unfold primeProxy
  split_ifs with hn
  · exact div_nonneg (Real.exp_nonneg _) (euler_defect_pos ht hn).le
  · exact le_rfl

/-- Exact value one at genuine primes, at EVERY nonnegative parameter. -/
theorem primeProxy_prime {t : ℝ} (_ht : 0 ≤ t) {p : ℕ} (hp : p.Prime) :
    primeProxy t p = 1 := by
  have he : expDivisorSum t p = 1-Real.exp (-t*Real.log p) := by
    simpa only [pow_one] using expDivisorSum_prime_pow t hp (by decide : 0 < 1)
  rw [primeProxy, if_pos hp.one_lt, he]
  have hpos := Real.exp_pos (-t*Real.log p)
  field_simp
  ring

/-- For a composite output, the least prime divisor is at most its square
root. This supplies a fixed-parameter decaying error, without a moving
t*log(n) window. -/
theorem primeProxy_composite_bound {t : ℝ} (ht : 0 ≤ t) {n : ℕ}
    (hn : 1 < n) (hnp : ¬ n.Prime) :
    primeProxy t n ≤ Real.exp (-(t/2)*Real.log n) := by
  have hp := Nat.minFac_prime (by omega : n ≠ 1)
  have hd := euler_defect_ge_factor ht (by omega : n ≠ 0)
    (Nat.mem_primeFactors.mpr ⟨hp, Nat.minFac_dvd n, by omega⟩)
  have hsq := Nat.minFac_sq_le_self (by omega : 0 < n) hnp
  have hlogs : 2*Real.log n.minFac ≤ Real.log n := by
    have hh := Real.log_le_log
      (show (0:ℝ) < (n.minFac^2:ℕ) by exact_mod_cast Nat.pow_pos hp.pos)
      (Nat.cast_le.mpr hsq)
    rw [Nat.cast_pow, Real.log_pow] at hh
    simpa only [Nat.cast_ofNat] using hh
  have hlow : Real.exp (-(t/2)*Real.log n) ≤ 1-expDivisorSum t n := by
    apply le_trans _ hd
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_le_mul_of_nonneg_left hlogs ht]
  have he : Real.exp (-t*Real.log n) = (Real.exp (-(t/2)*Real.log n))^2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [primeProxy, if_pos hn]
  apply (div_le_iff₀ (euler_defect_pos ht hn)).mpr
  rw [he]
  have hh := mul_le_mul_of_nonneg_left hlow (Real.exp_nonneg (-(t/2)*Real.log n))
  nlinarith only [hh]

/-- At parameter four the error is bounded by the convergent square
reciprocal series, including the exceptional inputs zero and one. -/
theorem primeProxy_four_nonprime {n : ℕ} (hnp : ¬ n.Prime) :
    primeProxy 4 n ≤ ((n:ℝ)^2)⁻¹ := by
  by_cases hn : 1 < n
  · have hh := primeProxy_composite_bound (by norm_num : (0:ℝ) ≤ 4) hn hnp
    have hpos : (0:ℝ) < n := Nat.cast_pos.mpr (by omega)
    have he : Real.exp (-(4/2:ℝ)*Real.log n) = ((n:ℝ)^2)⁻¹ := by
      norm_num only [show (4/2:ℝ) = 2 by norm_num]
      rw [neg_mul, Real.exp_neg, show (2:ℝ)*Real.log n = Real.log ((n:ℝ)^2) by
        rw [Real.log_pow]; norm_num, Real.exp_log (sq_pos_of_pos hpos)]
    exact hh.trans_eq he
  · simp only [primeProxy, if_neg hn]
    positivity

/-- This expansion is nonnegative for t>=0. It is only a pointwise
geometric-series identity, not an estimate uniform in the moment index. -/
theorem hasSum_primeProxy {t : ℝ} (ht : 0 ≤ t) {n : ℕ} (hn : 1 < n) :
    HasSum (fun j : ℕ => Real.exp (-t*Real.log n)*(expDivisorSum t n)^j)
      (primeProxy t n) := by
  have hnorm : ‖expDivisorSum t n‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (expDivisorSum_nonneg ht n)]
    linarith only [euler_defect_pos ht hn]
  have hh := (hasSum_geometric_of_norm_lt_one hnorm).mul_left (Real.exp (-t*Real.log n))
  simpa only [primeProxy, if_pos hn, div_eq_mul_inv] using hh

/-- Although the full proxy equals one at a prime p, its first J moments
capture at most J/p^4. Thus fixed-moment means cannot be passed to the full
prime-detecting series without additional uniform control. -/
theorem prime_truncated_proxy_bound {p : ℕ} (hp : p.Prime) (J : ℕ) :
    (∑ j ∈ range J, Real.exp (-(4:ℝ)*Real.log p)*(expDivisorSum 4 p)^j) ≤
      (J:ℝ)/(p:ℝ)^4 := by
  have he0 := expDivisorSum_nonneg (by norm_num : (0:ℝ) ≤ 4) p
  have he1 : expDivisorSum 4 p ≤ 1 := by
    linarith only [euler_defect_pos (by norm_num : (0:ℝ) ≤ 4) hp.one_lt]
  have hs : (∑ j ∈ range J, Real.exp (-(4:ℝ)*Real.log p)*(expDivisorSum 4 p)^j) ≤
      ∑ j ∈ range J, Real.exp (-(4:ℝ)*Real.log p) := by
    apply sum_le_sum
    intro j hj
    exact (mul_le_mul_of_nonneg_left (pow_le_one₀ he0 he1) (Real.exp_nonneg _)).trans_eq
      (mul_one _)
  have hexp : Real.exp (-(4:ℝ)*Real.log p) = ((p:ℝ)^4)⁻¹ := by
    rw [neg_mul, Real.exp_neg, show (4:ℝ)*Real.log p = Real.log ((p:ℝ)^4) by
      rw [Real.log_pow]; norm_num,
      Real.exp_log (pow_pos (Nat.cast_pos.mpr hp.pos) 4)]
  simpa only [sum_const, card_range, nsmul_eq_mul, hexp, div_eq_mul_inv] using hs

noncomputable def primeProxyWeight (α : ℝ) (n : ℕ) : ℝ :=
  if n.Prime then primeProxy 4 (floorMul α n) else 0

noncomputable def primePairIndicator (α : ℝ) (n : ℕ) : ℝ :=
  if n.Prime ∧ (floorMul α n).Prime then 1 else 0

noncomputable def proxyError (α : ℝ) (n : ℕ) : ℝ :=
  primeProxyWeight α n-primePairIndicator α n

lemma proxyError_bounds {α : ℝ} (hα : 1 ≤ α) (n : ℕ) :
    0 ≤ proxyError α n ∧ proxyError α n ≤ ((n:ℝ)^2)⁻¹ := by
  classical
  by_cases hp : n.Prime
  · by_cases hq : (floorMul α n).Prime
    · simp [proxyError, primeProxyWeight, primePairIndicator, hp, hq,
        primeProxy_prime (by norm_num : (0:ℝ) ≤ 4) hq]
    · have hbound := primeProxy_four_nonprime hq
      have hcast : (n:ℝ) ≤ floorMul α n := Nat.cast_le.mpr (self_le_floorMul hα n)
      have hpos : (0:ℝ) < n := Nat.cast_pos.mpr hp.pos
      have hinv : (((floorMul α n : ℕ):ℝ)^2)⁻¹ ≤ ((n:ℝ)^2)⁻¹ := by
        simpa only [one_div] using one_div_le_one_div_of_le (sq_pos_of_pos hpos)
          (pow_le_pow_left₀ hpos.le hcast 2)
      simpa only [proxyError, primeProxyWeight, primePairIndicator, hp, hq,
        and_false, if_false, if_true, sub_zero] using
          And.intro (primeProxy_nonneg (by norm_num : (0:ℝ) ≤ 4) (floorMul α n))
            (hbound.trans hinv)
  · simp [proxyError, primeProxyWeight, primePairIndicator, hp]

/-- The total composite proxy error is summable with no irrationality
hypothesis and no selected-scale restriction. -/
theorem summable_proxyError {α : ℝ} (hα : 1 ≤ α) : Summable (proxyError α) := by
  exact (Real.summable_nat_pow_inv.mpr (by decide : 1 < 2)).of_nonneg_of_le
    (fun n => (proxyError_bounds hα n).1) (fun n => (proxyError_bounds hα n).2)

/-- The fixed nonlinear series is nonsummable EXACTLY when there are
infinitely many genuine prime pairs. This does not prove nonsummability. -/
theorem summable_primeProxyWeight_iff_finite {α : ℝ} (hα : 1 ≤ α) :
    Summable (primeProxyWeight α) ↔
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
    have hval : primeProxyWeight α p = 1 := by
      simp only [primeProxyWeight, if_pos hp.1,
        primeProxy_prime (by norm_num : (0:ℝ) ≤ 4) hp.2]
    rw [hval] at hh
    exact (lt_irrefl 1) hh
  · intro hfin
    have hi : Summable (primePairIndicator α) := by
      apply summable_of_ne_finset_zero (s := hfin.toFinset)
      intro p hp
      have hnot : ¬ (p.Prime ∧ (floorMul α p).Prime) := by
        simpa only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] using hp
      simp [primePairIndicator, hnot]
    apply (hi.add (summable_proxyError hα)).congr
    intro n
    unfold proxyError
    ring

#print axioms primeProxy_prime
#print axioms primeProxy_composite_bound
#print axioms primeProxy_four_nonprime
#print axioms hasSum_primeProxy
#print axioms prime_truncated_proxy_bound
#print axioms summable_proxyError
#print axioms summable_primeProxyWeight_iff_finite

end Erdos972NonlinearPrimeProxy
