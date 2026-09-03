import Submission.HigherDivisorWeights

/-!
# A subexponential cost for higher divisor weights

The product cost is retained before taking logarithms. In particular it is
not replaced by an exponential in the divisor order. These are upper-bound
lemmas, not the missing lower moment on shifted primes.
-/

open Nat Filter
open scoped Classical BigOperators Topology

namespace Erdos821.HigherDivisors

noncomputable def logEulerCost (k : ℕ) : ℝ :=
  ∑' n : ℕ, Real.log (1+8*(k : ℝ)*((n : ℝ)^2)⁻¹)

noncomputable def eulerCost (k : ℕ) : ℝ := Real.exp (logEulerCost k)

lemma logEulerCost_summable (k : ℕ) :
    Summable (fun n : ℕ => Real.log (1+8*(k : ℝ)*((n : ℝ)^2)⁻¹)) := by
  apply Real.summable_log_one_add_of_summable
  exact (Real.summable_nat_pow_inv.mpr (by decide : 1 < 2)).mul_left (8*(k : ℝ))

lemma logEulerCost_nonneg (k : ℕ) : 0 ≤ logEulerCost k := by
  apply tsum_nonneg
  intro n
  apply Real.log_nonneg
  exact le_add_of_nonneg_right (by positivity)

lemma eulerCost_pos (k : ℕ) : 0 < eulerCost k := Real.exp_pos _

lemma eulerCost_ge_one (k : ℕ) : 1 ≤ eulerCost k := by
  exact Real.one_le_exp_iff.mpr (logEulerCost_nonneg k)

lemma finite_euler_product_le (k : ℕ) (S : Finset ℕ) :
    (∏ p ∈ S, (1+8*(k : ℝ)*((p : ℝ)^2)⁻¹)) ≤ eulerCost k := by
  calc
    _ = Real.exp (∑ p ∈ S, Real.log (1+8*(k : ℝ)*((p : ℝ)^2)⁻¹)) := by
      rw [Real.exp_sum]
      apply Finset.prod_congr rfl
      intro p hp
      exact (Real.exp_log (by positivity)).symm
    _ ≤ _ := Real.exp_le_exp.mpr
      ((logEulerCost_summable k).sum_le_tsum S
        (fun p _ => Real.log_nonneg (le_add_of_nonneg_right (by positivity))))

lemma tendsto_log_affine_nat_div (a : ℝ) (ha : 0 ≤ a) :
    Tendsto (fun k : ℕ => Real.log (1+a*(k : ℝ))/(k : ℝ)) atTop (𝓝 0) := by
  rcases ha.eq_or_lt with ha | ha
  · subst a
    simp
  have ht : Tendsto (fun k : ℕ => 1+a*(k : ℝ)) atTop atTop :=
    tendsto_const_nhds.add_atTop (tendsto_natCast_atTop_atTop.const_mul_atTop ha)
  have h := (Real.tendsto_pow_log_div_mul_add_atTop a⁻¹ (-a⁻¹) 1 (inv_ne_zero ha.ne')).comp ht
  apply h.congr
  intro k
  dsimp only [Function.comp_def]
  rw [pow_one]
  congr 1
  field_simp
  ring

/-- Dividing the logarithmic product cost by the order tends to zero. -/
theorem tendsto_logEulerCost_div :
    Tendsto (fun k : ℕ => logEulerCost k/(k : ℝ)) atTop (𝓝 0) := by
  have hs : Summable (fun n : ℕ => 8*((n : ℝ)^2)⁻¹) :=
    (Real.summable_nat_pow_inv.mpr (by decide : 1 < 2)).mul_left 8
  have ht (n : ℕ) :
      Tendsto (fun k : ℕ => Real.log (1+8*(k : ℝ)*((n : ℝ)^2)⁻¹)/(k : ℝ))
        atTop (𝓝 (0 : ℝ)) := by
    convert tendsto_log_affine_nat_div (8*((n : ℝ)^2)⁻¹) (by positivity) using 1
    funext k
    congr 2
    ring
  have hb : ∀ᶠ k : ℕ in atTop, ∀ n : ℕ,
      ‖Real.log (1+8*(k : ℝ)*((n : ℝ)^2)⁻¹)/(k : ℝ)‖ ≤ 8*((n : ℝ)^2)⁻¹ := by
    filter_upwards [eventually_ge_atTop 1] with k hk n
    have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hx : 0 ≤ 8*(k : ℝ)*((n : ℝ)^2)⁻¹ := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg
      (Real.log_nonneg (by linarith : 1 ≤ 1+8*(k : ℝ)*((n : ℝ)^2)⁻¹)) hkR.le)]
    apply (div_le_iff₀ hkR).mpr
    have hlog := Real.log_le_sub_one_of_pos (by linarith : 0 < 1+8*(k : ℝ)*((n : ℝ)^2)⁻¹)
    nlinarith
  have h := tendsto_tsum_of_dominated_convergence hs ht hb
  simpa only [tsum_div_const, logEulerCost, tsum_zero] using h

/-- In particular the cost is eventually below exp(epsilon*k), for every
positive epsilon, uniformly over the finite prime set in the product. -/
theorem eventually_eulerCost_le_exp (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, eulerCost k ≤ Real.exp (ε*(k : ℝ)) := by
  filter_upwards [tendsto_logEulerCost_div.eventually_lt_const hε,
    eventually_ge_atTop 1] with k hk hk1
  apply Real.exp_le_exp.mpr
  exact ((div_lt_iff₀ (by exact_mod_cast (show 0 < k by omega) : (0 : ℝ) < k)).mp hk).le

lemma harmonicMoment_totient_ratio_le_cost (k A : ℕ) :
    (∑ n ∈ Finset.Icc 1 A, (tau (k+1) n : ℝ) *
      ((n : ℝ)/n.totient)^2 / (n : ℝ)) ≤
        eulerCost (k+1) * harmonicMoment (k+1) A := by
  apply (harmonicMoment_totient_ratio_le_product k A).trans
  calc
    _ ≤ harmonicMoment (k+1) A * eulerCost (k+1) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        mul_le_mul_of_nonneg_left (finite_euler_product_le (k+1) (A+1).primesBelow)
          (harmonicMoment_nonneg (k+1) A)
    _ = _ := mul_comm _ _

end Erdos821.HigherDivisors
