import Submission.SmoothDivisorTail
import Submission.SmoothCorrelationScale
import Submission.PrimeIntervalCounts

/-! Subtracting the truncated divisor sum at t=0 removes its constant term,
but the resulting truncation vanishes at every prime beyond its cutoff.
Its actual error has large mean square in the shrinking-parameter regime.
These are checks on this approximation, not a disproof of Erdos 972. -/
namespace Erdos972BalancedSmoothCutoff

open Finset Filter ArithmeticFunction
open scoped Topology
open Erdos972SmoothMangoldt Erdos972SmoothDivisorTail Erdos972SmoothCorrelationScale
open Erdos972PrimeIntervalCounts Erdos972PrimePowerError Erdos972ExponentialSum

noncomputable def balancedTruncation (t : ℝ) (D n : ℕ) : ℝ :=
  (truncatedExpSum t D n-truncatedExpSum 0 D n)/t

lemma truncatedExpSum_prime (t : ℝ) {D p : ℕ} (hp : p.Prime) (hDp : D < p) :
    truncatedExpSum t D p = if 1 ≤ D then 1 else 0 := by
  classical
  rw [truncatedExpSum, hp.divisors, sum_filter, sum_pair hp.ne_one.symm]
  simp [not_le.mpr hDp, dampedCoefficient]

/-- The prime contribution is entirely in the error of this balanced cutoff. -/
theorem balancedTruncation_prime (t : ℝ) {D p : ℕ} (hp : p.Prime) (hDp : D < p) :
    balancedTruncation t D p = 0 := by
  rw [balancedTruncation, truncatedExpSum_prime t hp hDp,
    truncatedExpSum_prime 0 hp hDp, sub_self, zero_div]

lemma smoothMangoldt_prime_lower {t : ℝ} (ht : 0 < t) {p : ℕ} (hp : p.Prime)
    (hsmall : t*Real.log p ≤ 1/4) :
    Real.log p/2 ≤ smoothMangoldt t p := by
  have hcard : p.divisors.card = 2 := by rw [hp.divisors, card_pair hp.ne_one.symm]
  have he := smoothMangoldt_error_bound ht (show t*Real.log p ≤ 1 by linarith)
  rw [ArithmeticFunction.vonMangoldt_apply_prime hp, hcard] at he
  have hl := Real.log_natCast_nonneg p
  have hh := mul_le_mul_of_nonneg_right hsmall hl
  have he' := (abs_le.mp he).1
  norm_num only [Nat.cast_ofNat] at he'
  nlinarith only [he', hh]

/-- A finite lower bound from the prime inputs alone. No assertion of prime
outputs is used. -/
theorem balanced_error_energy_lower {x D : ℕ} (hx : 2 ≤ x) (hD : D ≤ x)
    {t : ℝ} (ht : 0 < t) (hsmall : t*Real.log (2*x:ℕ) ≤ 1/4)
    (hcount : (x:ℝ)/(2*Real.log (2*x:ℕ)) ≤ (primesBetween x (2*x)).card) :
    (x:ℝ)*Real.log x/16 ≤
      ∑ n ∈ Ioc 0 (2*x), (smoothMangoldt t n-balancedTruncation t D n)^2 := by
  have hxR : (1:ℝ) < x := by exact_mod_cast (show 1 < x by omega)
  have hlogx : 0 < Real.log x := Real.log_pos hxR
  have hlog2x : 0 < Real.log (2*x:ℕ) := Real.log_pos (by push_cast; linarith)
  have hlog : Real.log (2*x:ℕ) ≤ 2*Real.log x := by
    rw [Nat.cast_mul, Real.log_mul (by norm_num) (by positivity)]
    norm_num only [Nat.cast_ofNat]
    have hh := Real.log_le_log (by norm_num : (0:ℝ)<2) (Nat.cast_le.mpr hx)
    linarith only [hh]
  have hsub : primesBetween x (2*x) ⊆ Ioc 0 (2*x) := by
    intro p hp
    obtain ⟨hxp, hpx, _⟩ := mem_primesBetween.mp hp
    exact mem_Ioc.mpr ⟨by omega, hpx⟩
  have hpoint (p : ℕ) (hp : p ∈ primesBetween x (2*x)) :
      (Real.log x/2)^2 ≤ (smoothMangoldt t p-balancedTruncation t D p)^2 := by
    obtain ⟨hxp, hpx, hprime⟩ := mem_primesBetween.mp hp
    rw [balancedTruncation_prime t hprime (hD.trans_lt hxp), sub_zero]
    have hlogp : Real.log x ≤ Real.log p := monotone_log_natCast hxp.le
    have hsmallp : t*Real.log p ≤ 1/4 :=
      (mul_le_mul_of_nonneg_left (monotone_log_natCast hpx) ht.le).trans hsmall
    have hpbound := smoothMangoldt_prime_lower ht hprime hsmallp
    exact pow_le_pow_left₀ (by positivity) (by linarith) 2
  have hcard : (x:ℝ)/(4*Real.log x) ≤ (primesBetween x (2*x)).card := by
    apply le_trans _ hcount
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) (by linarith)
  calc
    _ = ((x:ℝ)/(4*Real.log x))*(Real.log x/2)^2 := by field_simp; ring
    _ ≤ (primesBetween x (2*x)).card*(Real.log x/2)^2 :=
      mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
    _ = ∑ p ∈ primesBetween x (2*x), (Real.log x/2)^2 := by simp
    _ ≤ ∑ p ∈ primesBetween x (2*x), (smoothMangoldt t p-balancedTruncation t D p)^2 := sum_le_sum hpoint
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => sq_nonneg _)

lemma comparison_parameter_quarter (α : ℝ) (N : ℕ) :
    smoothingParameter α N * Real.log (floorMul α N) ≤ 1/4 := by
  let L := Real.log (floorMul α N)
  have hL : 0 ≤ L := Real.log_natCast_nonneg _
  have hb : 1+5*L ≤ (1+L)^5 := by
    simpa using one_add_mul_le_pow (a := L) (by linarith : -2 ≤ L) 5
  change (1/(1+L)^5)*L ≤ 1/4
  rw [one_div_mul_eq_div]
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith only [hb, hL]

/-- The actual normalized mean-square error diverges, even after subtracting
the truncated t=0 term. This rules out an o(N) energy justification for
this particular cutoff; it does not rule out a signed cross estimate. -/
theorem balanced_error_energy_tendsto_atTop {α : ℝ} (hα : 1 ≤ α) (D : ℕ → ℕ)
    (hD : ∀ᶠ x : ℕ in atTop, D x ≤ x) :
    Tendsto (fun x : ℕ =>
      (∑ n ∈ Ioc 0 (2*x),
        (smoothMangoldt (smoothingParameter α (2*x)) n-
          balancedTruncation (smoothingParameter α (2*x)) (D x) n)^2)/(2*x:ℕ))
      atTop atTop := by
  have hlog : Tendsto (fun x : ℕ => Real.log x/32) atTop atTop := by
    have hh := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop
      (by norm_num : (0:ℝ) < 1/32)
    simpa only [Function.comp_apply, div_eq_mul_inv, one_div, mul_comm, one_mul, mul_one] using hh
  apply tendsto_atTop_mono' atTop _ hlog
  filter_upwards [eventually_ge_atTop (2:ℕ), hD, eventually_prime_interval_counts] with x hx hDx hcount
  have ht : 0 < smoothingParameter α (2*x) := smoothingParameter_pos α (2*x)
  have hsmall : smoothingParameter α (2*x)*Real.log (2*x:ℕ) ≤ 1/4 := by
    apply le_trans _ (comparison_parameter_quarter α (2*x))
    exact mul_le_mul_of_nonneg_left (monotone_log_natCast (self_le_floorMul hα (2*x))) ht.le
  have he := balanced_error_energy_lower hx hDx ht hsmall hcount.2.2
  have hden : (0:ℝ) < ((2*x:ℕ):ℝ) := by positivity
  apply (le_div_iff₀ hden).mpr
  have heq : (Real.log x/32)*((2*x:ℕ):ℝ) = (x:ℝ)*Real.log x/16 := by push_cast; ring
  rw [heq]
  exact he

#print axioms balancedTruncation_prime
#print axioms balanced_error_energy_lower
#print axioms balanced_error_energy_tendsto_atTop

end Erdos972BalancedSmoothCutoff
