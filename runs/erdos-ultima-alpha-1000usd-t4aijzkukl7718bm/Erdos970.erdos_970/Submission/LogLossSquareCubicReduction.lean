import Submission.LogLossSquareCubicSeed

/-! A conditional quadratic reduction with logarithmically sublinear
exponential loss. The square-cubic correlation premise remains UNPROVED.
None of the theorems here asserts the original conjecture unconditionally. -/
namespace Erdos970.GapAverages
open Finset Real Filter
set_option maxHeartbeats 2400000

/-- An eventual budget-uniform correlation premise. It is not established
here. The loss exp(C*k/log(k)^B) is larger asymptotically than every fixed
sublinear-power exponential loss. -/
def LogLossSquareCubicVoidBound (C : ℝ) (B : ℕ) : Prop :=
  ∀ᶠ k : ℕ in atTop, ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → P.card ≤ k →
    ∀ m : ℕ, k ≤ m → coveredFraction P (2*m)^2 ≤
      exp (C*(k : ℝ)/log (k : ℝ)^B)*coveredFraction P m^3

lemma dyadic_phase_entropy (t : ℕ) (ht : 0 < t) :
    log (((2 : ℝ)^t+2)^14) ≤ 42*(t : ℝ) := by
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hK : (2 : ℝ) ≤ (2 : ℝ)^t := by
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (show 1 ≤ t from ht)
  have hlog2 : log (2 : ℝ) ≤ 1 := le_trans log_two_lt_d9.le (by norm_num)
  have hh := log_le_log (by positivity : (0 : ℝ) < (2 : ℝ)^t+2)
    (show (2 : ℝ)^t+2 ≤ 2*(2 : ℝ)^t by linarith only [hK])
  rw [log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity),log_pow] at hh
  have hm := mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg t)
  rw [log_pow]
  norm_num only [Nat.cast_ofNat]
  nlinarith only [hh,hm,hlog2,ht1]

lemma logIteration_entropy_small (b t : ℕ)
    (ht : 1075200*2^b+1 ≤ t) :
    (2 : ℝ)^t*log (((2 : ℝ)^t+2)^14) <
      logIterationSeed b (b+2) t*(5 : ℝ)^logIterationSteps (b+2) t := by
  have ht0 : 0 < t := by omega
  have htR : (0 : ℝ) < t := by exact_mod_cast ht0
  have hlarge : 1075200*(2 : ℝ)^b < t := by exact_mod_cast ht
  have hent := mul_le_mul_of_nonneg_left (dyadic_phase_entropy t ht0)
    (show 0 ≤ (2 : ℝ)^t by positivity)
  have hmid : (2 : ℝ)^t*(42*(t : ℝ)) < (2 : ℝ)^t*(t : ℝ)^2/(25600*2^b) := by
    apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 25600*2^b)).mpr
    have hh := mul_lt_mul_of_pos_left hlarge (show 0 < (2 : ℝ)^t*(t : ℝ) by positivity)
    convert hh using 1 <;> ring
  exact (hent.trans_lt hmid).trans_le (logIteration_rate_gain (b+2) t b ht0 rfl)

/-- CONDITIONAL exclusion on dyadic prime budgets. The initial interval is
smaller than the final square by a fixed power of the logarithm. -/
theorem eventually_dyadic_quadratic_of_log_loss_square_cubic (b : ℕ)
    (hseed : ∀ᶠ k : ℕ in atTop, ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → P.card ≤ k →
      coveredFraction P k ≤ exp (-sqrt (k : ℝ)/(800*log (k : ℝ)^b)))
    (C : ℝ) (hC : 0 ≤ C)
    (h : LogLossSquareCubicVoidBound C (b+8*(b+2)+1)) :
    ∀ᶠ t : ℕ in atTop, jacobsthalFunction (2^t) ≤ (2^t)^2 := by
  have hstep := (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < (2 : ℕ))).eventually h
  filter_upwards [hstep,eventually_logIteration_scaled_seed b (b+2) C hC hseed,
    eventually_logIterationIndex_small (b+2),eventually_ge_atTop (1075200*2^b+1)]
      with t hstep hbase hidx ht
  have ht0 : 0 < t := by omega
  let K := (2 : ℕ)^t
  let m := logIterationLength (b+2) t
  let j := logIterationSteps (b+2) t
  have hbudget := logIterationLength_budget (b+2) t hidx
  have hKm : K ≤ m := hbudget.1
  have hlen : 16^j*m=K^2 := hbudget.2.1
  apply (jacobsthalFunction_le_iff K (K^2)).mpr
  by_contra hbad
  obtain ⟨P,hP,hPk,r,hcov⟩ := (not_isJacobsthalBound_iff_cover K (K^2)).mp hbad
  obtain ⟨Q,s,hQ,hQk,hcap,hcov'⟩ := BoundedPrimeCover.normalize hP hPk hcov
  let a := exp (C*(K : ℝ)/log (K : ℝ)^(b+8*(b+2)+1))
  have hK1 : 1 ≤ K := Nat.one_le_pow _ _ (by omega)
  have ha : 1 ≤ a := by
    apply one_le_exp_iff.mpr
    exact div_nonneg (mul_nonneg hC (Nat.cast_nonneg K))
      (pow_nonneg (log_natCast_nonneg K) _)
  have hs : ∀ n, m ≤ n → coveredFraction Q (2*n)^2 ≤ a*coveredFraction Q n^3 := by
    intro n hn
    exact hstep Q hQ hQk n (hKm.trans hn)
  have hscaled : a*coveredFraction Q m ≤ exp (-logIterationSeed b (b+2) t) := by
    simpa only [a,K,m,Nat.cast_pow,Nat.cast_ofNat] using hbase Q hQ hQk
  have htail := square_cubic_scaled_tail Q m j a (logIterationSeed b (b+2) t) ha
    (logIterationSeed_pos b (b+2) t ht0).le hs hscaled
  rw [hlen] at htail
  have hent : (K : ℝ)*log (((K : ℝ)+2)^14) <
      logIterationSeed b (b+2) t*(5 : ℝ)^j := by
    simpa only [K,j,Nat.cast_pow,Nat.cast_ofNat] using logIteration_entropy_small b t ht
  obtain ⟨x,hx,havoid⟩ := survivor_of_exponential_tail_of_cap hQ hQk
    (one_le_pow₀ (by have := Nat.cast_nonneg (α := ℝ) K; linarith : (1 : ℝ) ≤ (K : ℝ)+2))
    (fun q hq => scaled_quadratic_cap hK1 (by simpa only [one_mul] using hcap q hq))
    (by simpa only [neg_mul] using htail) hent s
  obtain ⟨q,hq,hxq⟩ := hcov' x hx
  exact havoid q hq hxq

lemma quadratic_bound_of_eventually_dyadic
    (h : ∀ᶠ t : ℕ in atTop, jacobsthalFunction (2^t) ≤ (2^t)^2) :
    ∃ A > (0 : ℝ), ∀ k : ℕ, 0 < k → (jacobsthalFunction k : ℝ) ≤ A*k^2 := by
  obtain ⟨T,hT⟩ := eventually_atTop.mp h
  apply quadratic_bound_of_eventually_scaled (D := 4) (by omega)
  filter_upwards [eventually_ge_atTop (2^T)] with k hk
  have hk0 : 0 < k := (by positivity : 0 < (2 : ℕ)^T).trans_le hk
  let t := Nat.log 2 k+1
  have hkt : k < 2^t := Nat.lt_pow_succ_log_self (by norm_num) k
  have hTk : T ≤ t := by
    have hh : 2^T ≤ (2 : ℕ)^t := hk.trans hkt.le
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < (2 : ℕ))).mp hh
  have hsmall : 2^t ≤ 2*k := by
    have hh := Nat.pow_log_le_self 2 hk0.ne'
    dsimp only [t]
    rw [pow_succ]
    omega
  have hh := (jacobsthalFunction_strictMono.monotone hkt.le).trans (hT t hTk)
  apply hh.trans
  have hp := Nat.pow_le_pow_left hsmall 2
  simpa only [mul_pow,show (2 : ℕ)^2=4 by norm_num] using hp

/-- There is one fixed loss exponent B for which the stated correlation
premise would suffice. This theorem retains that premise explicitly. -/
theorem exists_log_loss_square_cubic_reduction : ∃ B : ℕ, 0 < B ∧
    ∀ C : ℝ, 0 ≤ C → LogLossSquareCubicVoidBound C B →
      ∃ A > (0 : ℝ), ∀ k : ℕ, 0 < k → (jacobsthalFunction k : ℝ) ≤ A*k^2 := by
  obtain ⟨b,hb,hseed⟩ := exists_log_critical_linear_void
  refine ⟨b+8*(b+2)+1,by omega,fun C hC h => ?_⟩
  exact quadratic_bound_of_eventually_dyadic
    (eventually_dyadic_quadratic_of_log_loss_square_cubic b hseed C hC h)

#print axioms eventually_dyadic_quadratic_of_log_loss_square_cubic
#print axioms exists_log_loss_square_cubic_reduction
end Erdos970.GapAverages
