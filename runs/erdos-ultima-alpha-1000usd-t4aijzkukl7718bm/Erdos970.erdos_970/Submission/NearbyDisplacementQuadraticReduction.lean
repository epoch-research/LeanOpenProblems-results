import Submission.NearbyDisplacementCriterion

/-! A conditional reduction of the unchanged conjecture to an averaged
nearby-displacement estimate. The local covariance premise remains UNPROVED.
Far-translation counterexamples do not contradict this local premise. -/
namespace Erdos970.GapAverages
open Finset Real Filter
set_option maxHeartbeats 2200000

lemma ternary_log_iteration_comparison (r t : ℕ) :
    3^(40*logIterationIndex r t) ≤ 16^logIterationSteps r t ∧
      5^logIterationSteps r t ≤ 2^(40*logIterationIndex r t) := by
  have h1 := Nat.pow_le_pow_left (show (3 : ℕ)^40 ≤ 16^16 by norm_num)
    (logIterationIndex r t)
  have h2 := Nat.pow_le_pow_left (show (5 : ℕ)^16 ≤ 2^40 by norm_num)
    (logIterationIndex r t)
  simpa only [← pow_mul,logIterationSteps] using And.intro h1 h2

/-- The currently verified logarithmic-loss seed suffices if the local
covariance premise holds. No covariance estimate is supplied here. -/
theorem eventually_dyadic_quadratic_of_nearby_covariance (b : ℕ)
    (hseed : ∀ᶠ k : ℕ in atTop, ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → P.card ≤ k →
      coveredFraction P k ≤ exp (-sqrt (k : ℝ)/(800*log (k : ℝ)^b)))
    (C : ℝ) (hC : 0 ≤ C)
    (h : LogLossNearbyCovarianceBound C (b+8*(b+2)+1)) :
    ∀ᶠ t : ℕ in atTop, jacobsthalFunction (2^t) ≤ (2^t)^2 := by
  have hstep := (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < (2 : ℕ))).eventually h
  filter_upwards [hstep,eventually_logIteration_scaled_seed b (b+2) C hC hseed,
    eventually_logIterationIndex_small (b+2),eventually_ge_atTop (1075200*2^b+1)]
      with t hstep hbase hidx ht
  have ht0 : 0 < t := by omega
  let K := (2 : ℕ)^t
  let m := logIterationLength (b+2) t
  let j := 40*logIterationIndex (b+2) t
  let jold := logIterationSteps (b+2) t
  have hbudget := logIterationLength_budget (b+2) t hidx
  have hKm : K ≤ m := hbudget.1
  have hlen : 16^jold*m=K^2 := hbudget.2.1
  have hcompare := ternary_log_iteration_comparison (b+2) t
  have hlength : 3^j*m ≤ K^2 := by
    rw [← hlen]
    exact Nat.mul_le_mul_right m hcompare.1
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
  have hs : ∀ n, m ≤ n → coveredFraction Q (3*n) ≤ a*coveredFraction Q n^2 := by
    intro n hn
    exact void_triple_of_nearby_covariance Q hQ n (by omega) a
      (hstep Q hQ hQk n (hKm.trans hn))
  have hscaled : a*coveredFraction Q m ≤ exp (-logIterationSeed b (b+2) t) := by
    simpa only [a,K,m,Nat.cast_pow,Nat.cast_ofNat] using hbase Q hQ hQk
  have htail := ternary_scaled_tail Q m j a (logIterationSeed b (b+2) t) ha hs hscaled
  have htail' : coveredFraction Q (K^2) ≤
      exp (-logIterationSeed b (b+2) t*(5 : ℝ)^jold) := by
    apply ((void_antitone_length Q hlength).trans htail).trans
    apply exp_le_exp.mpr
    have hpow : (5 : ℝ)^jold ≤ (2 : ℝ)^j := by exact_mod_cast hcompare.2
    have hh := mul_le_mul_of_nonneg_left hpow (logIterationSeed_pos b (b+2) t ht0).le
    linarith only [hh]
  have hent : (K : ℝ)*log (((K : ℝ)+2)^14) <
      logIterationSeed b (b+2) t*(5 : ℝ)^jold := by
    simpa only [K,jold,Nat.cast_pow,Nat.cast_ofNat] using logIteration_entropy_small b t ht
  obtain ⟨x,hx,havoid⟩ := survivor_of_exponential_tail_of_cap hQ hQk
    (one_le_pow₀ (by have := Nat.cast_nonneg (α := ℝ) K; linarith : (1 : ℝ) ≤ (K : ℝ)+2))
    (fun q hq => scaled_quadratic_cap hK1 (by simpa only [one_mul] using hcap q hq))
    (by simpa only [neg_mul] using htail') hent s
  obtain ⟨q,hq,hxq⟩ := hcov' x hx
  exact havoid q hq hxq

/-- A single fixed logarithmic loss exponent suffices in the local averaged
covariance premise. That premise is retained explicitly in the conclusion. -/
theorem exists_nearby_covariance_quadratic_reduction : ∃ B : ℕ, 0 < B ∧
    ∀ C : ℝ, 0 ≤ C → LogLossNearbyCovarianceBound C B →
      ∃ A > (0 : ℝ), ∀ k : ℕ, 0 < k → (jacobsthalFunction k : ℝ) ≤ A*k^2 := by
  obtain ⟨b,hb,hseed⟩ := exists_log_critical_linear_void
  refine ⟨b+8*(b+2)+1,by omega,fun C hC h => ?_⟩
  exact quadratic_bound_of_eventually_dyadic
    (eventually_dyadic_quadratic_of_nearby_covariance b hseed C hC h)

#print axioms eventually_dyadic_quadratic_of_nearby_covariance
#print axioms exists_nearby_covariance_quadratic_reduction
end Erdos970.GapAverages
