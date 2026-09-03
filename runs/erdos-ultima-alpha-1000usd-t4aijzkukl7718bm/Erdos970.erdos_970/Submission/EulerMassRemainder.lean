import Submission.EulerMassAsymptotic

/-! A uniform additive remainder for the Euler product. The reciprocal-prime
interval modulus yields an unspecified positive constant C and a finite A with
`|initialEulerMass n - C * log n| ≤ A` for every n ≥ 2. This estimate is auxiliary;
it is not a bound on the Jacobsthal function. -/
namespace Erdos970.FiniteSelberg
open Finset Real Filter
open scoped Topology
set_option maxHeartbeats 1200000

lemma abs_exp_sub_one_le_exp_abs (x : ℝ) :
    |exp x-1| ≤ exp |x| * |x| := by
  by_cases hx : 0 ≤ x
  · have he : 1 ≤ exp x := one_le_exp_iff.mpr hx
    rw [abs_of_nonneg hx, abs_of_nonneg (sub_nonneg.mpr he)]
    have h := mul_le_mul_of_nonneg_left (add_one_le_exp (-x)) (exp_pos x).le
    have hid : exp x*exp (-x) = 1 := by rw [← exp_add]; simp
    rw [hid] at h
    nlinarith only [h]
  · have hx : x ≤ 0 := le_of_not_ge hx
    have he : exp x ≤ 1 := exp_le_one_iff.mpr hx
    rw [abs_of_nonpos hx, abs_of_nonpos (sub_nonpos.mpr he)]
    have h := add_one_le_exp x
    have hh : 1 ≤ exp (-x) := one_le_exp_iff.mpr (by linarith)
    nlinarith only [h, mul_le_mul_of_nonneg_right hh (neg_nonneg.mpr hx)]

/-- Passing the uniform Cauchy modulus to its limit retains the explicit
reciprocal-logarithmic error, rather than just asserting convergence. -/
theorem exists_eulerLogPhase_remainder : ∃ c : ℝ,
    Tendsto eulerLogPhase atTop (𝓝 c) ∧ ∀ n : ℕ, 2 ≤ n →
      |eulerLogPhase n-c| ≤ (2*(WeightedMertens.boundConstant+1)+1)/log (n : ℝ) := by
  obtain ⟨c,hc⟩ := cauchySeq_tendsto_of_complete eulerLogPhase_cauchy
  refine ⟨c,hc,fun n hn => ?_⟩
  have hh : |c-eulerLogPhase n| ≤
      2*(WeightedMertens.boundConstant+1)/log (n : ℝ)+1/(n : ℝ) := by
    apply le_of_tendsto (hc.sub_const (eulerLogPhase n)).abs
    filter_upwards [eventually_ge_atTop n] with m hm
    exact eulerLogPhase_difference n m hn hm
  rw [abs_sub_comm] at hh
  have hl : 0 < log (n : ℝ) := log_pos (by exact_mod_cast (show 1 < n by omega))
  have hratio : 1/(n : ℝ) ≤ 1/log (n : ℝ) :=
    one_div_le_one_div_of_le hl (log_le_self (Nat.cast_nonneg n))
  calc
    _ ≤ 2*(WeightedMertens.boundConstant+1)/log (n : ℝ)+1/(n : ℝ) := hh
    _ ≤ 2*(WeightedMertens.boundConstant+1)/log (n : ℝ)+1/log (n : ℝ) :=
      add_le_add le_rfl hratio
    _ = _ := by ring

/-- Uniform additive O(1) remainder, with the same positive leading constant
at every index. No prime number theorem is used. -/
theorem exists_initialEulerMass_additive_remainder : ∃ C > (0 : ℝ), ∃ A > (0 : ℝ),
    ∀ n : ℕ, 2 ≤ n → |initialEulerMass n-C*log (n : ℝ)| ≤ A := by
  obtain ⟨c,hc,hrem⟩ := exists_eulerLogPhase_remainder
  let B : ℝ := 2*(WeightedMertens.boundConstant+1)+1
  let d : ℝ := B/log 2
  have hB : 0 < B := by dsimp [B]; linarith [WeightedMertens.boundConstant_pos]
  have hl2 : 0 < log 2 := log_pos (by norm_num)
  refine ⟨exp c,exp_pos c,exp c*exp d*B,by positivity,fun n hn => ?_⟩
  have hl : 0 < log (n : ℝ) := log_pos (by exact_mod_cast (show 1 < n by omega))
  have hlle : log 2 ≤ log (n : ℝ) := log_le_log (by norm_num) (by exact_mod_cast hn)
  have hsmall : |eulerLogPhase n-c| ≤ d :=
    (hrem n hn).trans (div_le_div_of_nonneg_left hB.le hl2 hlle)
  have hb : |exp (eulerLogPhase n-c)-1| ≤ exp d*(B/log (n : ℝ)) := by
    apply (abs_exp_sub_one_le_exp_abs _).trans
    exact mul_le_mul (exp_le_exp.mpr hsmall) (hrem n hn) (abs_nonneg _) (exp_pos _).le
  have hid : initialEulerMass n-exp c*log (n : ℝ) =
      (exp c*log (n : ℝ))*(exp (eulerLogPhase n-c)-1) := by
    rw [exp_sub, eulerLogPhase, exp_sub, exp_log (initialEulerMass_pos n), exp_log hl]
    field_simp [hl.ne',exp_ne_zero c]
    <;> ring
  rw [hid,abs_mul,abs_of_pos (mul_pos (exp_pos c) hl)]
  calc
    _ ≤ (exp c*log (n : ℝ))*(exp d*(B/log (n : ℝ))) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by field_simp <;> ring

#print axioms exists_eulerLogPhase_remainder
#print axioms exists_initialEulerMass_additive_remainder
end Erdos970.FiniteSelberg
