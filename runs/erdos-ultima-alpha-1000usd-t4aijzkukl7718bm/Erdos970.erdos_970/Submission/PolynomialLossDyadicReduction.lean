import Submission.LinearExposureTail
import Submission.PowerLossDyadicVoidReduction

/-! The improved linear-length exposure bound permits ANY fixed polynomial
loss in the long-interval dyadic premise. The premise is still unproved. -/
namespace Erdos970.GapAverages
open Finset Real Filter
set_option maxHeartbeats 1000000

lemma eventually_polynomial_log_budget (A α : ℝ) (hα : 0 ≤ α) :
    ∀ᶠ k : ℕ in atTop,
      log A + (α+1/2)*log ((k : ℝ)+2) ≤ (k : ℝ)^(31/80 : ℝ)/400 := by
  let c := |log A|+2*α+1
  have hc : 0 < c := by dsimp [c]; positivity
  have hs := tendsto_natCast_atTop_atTop.eventually
    ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 31/80)).def
      (show (0 : ℝ) < 1/(400*c) by positivity))
  filter_upwards [hs, eventually_ge_atTop 4] with k hs hk
  have hkR : (4 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hl : 0 ≤ log (k : ℝ) := log_nonneg (by linarith)
  have hl1 : 1 ≤ log (k : ℝ) := by
    have h4 : (1 : ℝ) ≤ log 4 := by
      rw [show (4 : ℝ)=2^2 by norm_num, log_pow]
      norm_num only [Nat.cast_ofNat]
      linarith only [log_two_gt_d9]
    exact h4.trans (log_le_log (by norm_num) hkR)
  have hs' : log (k : ℝ) ≤ (k : ℝ)^(31/80 : ℝ)/(400*c) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hl,
      abs_of_pos (rpow_pos_of_pos hk0 (31/80)), one_div, inv_mul_eq_div] using hs
  have hcs : c*log (k : ℝ) ≤ (k : ℝ)^(31/80 : ℝ)/400 := by
    have hh := (le_div_iff₀ (show (0 : ℝ) < 400*c by positivity)).mp hs'
    nlinarith only [hh]
  have hl2 : log ((k : ℝ)+2) ≤ 2*log (k : ℝ) := by
    have hh := log_le_log (by positivity : (0 : ℝ) < (k : ℝ)+2)
      (show (k : ℝ)+2 ≤ (k : ℝ)^2 by nlinarith only [hkR])
    simpa only [log_pow, Nat.cast_ofNat] using hh
  have ha := mul_le_mul_of_nonneg_left hl1 (abs_nonneg (log A))
  have hh := mul_le_mul_of_nonneg_left hl2 (show 0 ≤ α+1/2 by linarith)
  have hla := le_abs_self (log A)
  dsimp only [c] at hcs
  nlinarith only [hcs,ha,hh,hla]

/-- Every fixed polynomial factor can be absorbed at the starting length k.
Unlike the older variance-based result, α need not be less than one. -/
lemma eventually_polynomial_scaled_void_base (A α : ℝ) (hA : 0 < A) (hα : 0 ≤ α) :
    ∀ᶠ k : ℕ in atTop, ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → P.card ≤ k →
      (A*((k : ℝ)+2)^α)*coveredFraction P k ≤ exp (-log ((k : ℝ)+2)/2) := by
  filter_upwards [eventually_linear_stretched_void,
    eventually_polynomial_log_budget A α hα] with k hvoid hlog
  intro P hP hPk
  have hscale := mul_le_mul_of_nonneg_left (hvoid P hP hPk)
    (show 0 ≤ A*((k : ℝ)+2)^α by positivity)
  apply hscale.trans
  have he : A*((k : ℝ)+2)^α = exp (log A+α*log ((k : ℝ)+2)) := by
    rw [exp_add, exp_log hA, rpow_def_of_pos (by positivity)]
    congr 1
    congr 1
    ring
  rw [he, ← exp_add]
  exact exp_le_exp.mpr (by linarith only [hlog])

lemma polynomial_loss_dyadic_tail {A α : ℝ} (hA : 1 ≤ A) (hα : 0 ≤ α)
    (h : PowerLossDyadicVoidBound A α) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (k j : ℕ) (hk : P.card ≤ k)
    (hbase : (A*((k : ℝ)+2)^α)*coveredFraction P k ≤ exp (-log ((k : ℝ)+2)/2)) :
    coveredFraction P (2^j*k) ≤ exp (-(log ((k : ℝ)+2)*(2 : ℝ)^j/2)) := by
  let a := A*((k : ℝ)+2)^α
  have hpow : 1 ≤ ((k : ℝ)+2)^α := one_le_rpow (by have := Nat.cast_nonneg (α := ℝ) k; linarith) hα
  have ha : 1 ≤ a := by dsimp [a]; nlinarith only [hA,hpow]
  have hstep : ∀ m : ℕ, k ≤ m → coveredFraction P (2*m) ≤ a*coveredFraction P m^2 := by
    intro m hm
    apply (h P hP m (hk.trans hm)).trans
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply mul_le_mul_of_nonneg_left _ (by linarith : 0 ≤ A)
    apply rpow_le_rpow (by positivity) _ hα
    have hh : (P.card : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hi := local_dyadic_iteration P k a (by linarith) hstep j
  have hp := pow_le_pow_left₀ (mul_nonneg (by linarith : 0 ≤ a) (void_nonneg P k)) hbase (2^j)
  have hv := mul_le_mul_of_nonneg_right ha (void_nonneg P (2^j*k))
  simp only [one_mul] at hv
  calc
    _ ≤ (a*coveredFraction P k)^(2^j) := hv.trans hi
    _ ≤ (exp (-log ((k : ℝ)+2)/2))^(2^j) := hp
    _ = _ := by rw [← exp_nat_mul]; congr 1; push_cast; ring

/-- CONDITIONAL: a fixed polynomial loss of any degree in long doubling
would settle the original quadratic conjecture. No doubling premise is proved. -/
theorem eventually_quadratic_of_polynomial_dyadic {A α : ℝ}
    (hA : 1 ≤ A) (hα : 0 ≤ α) (h : PowerLossDyadicVoidBound A α) :
    ∀ᶠ k : ℕ in atTop, jacobsthalFunction k ≤ 128*k^2 := by
  filter_upwards [eventually_polynomial_scaled_void_base A α (by linarith) hα,
    eventually_ge_atTop 128] with k hbase hk128
  have hk : 0 < k := by omega
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  let j := Nat.log 2 (128*k)
  have hlow : 128*k < 2^(j+1) := Nat.lt_pow_succ_log_self (by norm_num) (128*k)
  have hupp : 2^j ≤ 128*k := Nat.pow_log_le_self 2 (by positivity : 128*k ≠ 0)
  have hlow' : 64*k < 2^j := by rw [pow_succ] at hlow; omega
  let m := 2^j*k
  have hm : m ≤ 128*k^2 := by dsimp [m]; nlinarith
  apply (jacobsthalFunction_le_iff k (128*k^2)).mpr
  by_contra hbad
  obtain ⟨P,hP,hPk,r,hcov⟩ := (not_isJacobsthalBound_iff_cover k (128*k^2)).mp hbad
  obtain ⟨Q,s,hQ,hQk,hcap,hcov'⟩ := BoundedPrimeCover.normalize hP hPk hcov
  have htail := polynomial_loss_dyadic_tail hA hα h Q hQ k j hQk (hbase Q hQ hQk)
  have hL : 0 < log ((k : ℝ)+2) := log_pos (by linarith)
  have hbudget : (k : ℝ)*log (((k : ℝ)+2)^14) <
      log ((k : ℝ)+2)*(2 : ℝ)^j/2 := by
    have hl : 64*(k : ℝ) < (2 : ℝ)^j := by exact_mod_cast hlow'
    have hh := mul_lt_mul_of_pos_right hl hL
    rw [log_pow]
    norm_num only [Nat.cast_ofNat]
    nlinarith [mul_pos hkR hL]
  obtain ⟨x,hx,havoid⟩ := survivor_of_exponential_tail_of_cap hQ hQk
    (one_le_pow₀ (by linarith : (1 : ℝ) ≤ (k : ℝ)+2))
    (fun q hq => scaled_quadratic_cap hk128 (hcap q hq)) htail hbudget s
  obtain ⟨q,hq,hxq⟩ := hcov' x (hx.trans_le hm)
  exact havoid q hq hxq

theorem quadratic_bound_of_polynomial_dyadic {A α : ℝ}
    (hA : 1 ≤ A) (hα : 0 ≤ α) (h : PowerLossDyadicVoidBound A α) :
    ∃ C > (0 : ℝ), ∀ k : ℕ, 0 < k → (jacobsthalFunction k : ℝ) ≤ C*k^2 :=
  quadratic_bound_of_eventually_scaled (by norm_num : 0 < (128 : ℕ))
    (eventually_quadratic_of_polynomial_dyadic hA hα h)

#print axioms eventually_polynomial_scaled_void_base
#print axioms quadratic_bound_of_polynomial_dyadic
end Erdos970.GapAverages
