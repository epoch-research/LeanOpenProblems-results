import Submission.PrimeCurrentAbsoluteBudget

/-! Unnormalized l2 convergence of the full vector of harmonic winning-prime
currents. This is weaker than the l1 tail tightness needed by the available
natural-density criterion; no upgrade to l1 is asserted. -/
namespace Erdos371
open Finset Filter
open scoped Topology
set_option autoImplicit false

lemma primeWinner_prime_of_pos (n : ℕ) (hn : 0<n) : (primeWinner n).Prime := by
  have he : primeWinner n=Nat.maxPrimeFac (n*(n+1)) :=
    (Nat.maxPrimeFac_mul hn.ne' (by omega : n+1≠0)).symm
  rw [he]
  apply Nat.prime_maxPrimeFac_of_one_lt
  nlinarith

lemma primeWinnerHarmonicTerm_zero_of_not_prime (p n : ℕ) (hp : ¬p.Prime) :
    primeWinnerHarmonicTerm p n=0 := by
  by_cases hn : n=0
  · subst n
    simp [primeWinnerHarmonicTerm]
  · have hw : primeWinner n≠p := fun he => hp (he ▸ primeWinner_prime_of_pos n (by omega))
    simp [primeWinnerHarmonicTerm,hw]

lemma primeWinnerHarmonicLimit_zero_of_not_prime (p : ℕ) (hp : ¬p.Prime) :
    primeWinnerHarmonicLimit p=0 := by
  simp only [primeWinnerHarmonicLimit,primeWinnerHarmonicTerm_zero_of_not_prime p _ hp,tsum_zero]

lemma rawPrimeWinnerHarmonic_zero_of_not_prime (p N : ℕ) (hp : ¬p.Prime) :
    rawPrimeWinnerHarmonic p N=0 := by
  simp only [rawPrimeWinnerHarmonic,primeWinnerHarmonicTerm_zero_of_not_prime p _ hp,sum_const_zero]

noncomputable def primeCurrentBudgetConstant : ℝ :=
  3*Real.exp 4*(1+8/Real.log 2)

lemma primeCurrentBudgetConstant_pos : 0<primeCurrentBudgetConstant := by
  have hl2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  unfold primeCurrentBudgetConstant
  positivity

lemma prime_current_log_budget_le_rpow (p : ℕ) (hp : 0<p) :
    3*Real.exp 4*(1+Real.log (p+1 : ℝ)/Real.log 2)/p ≤
      primeCurrentBudgetConstant*(p : ℝ)^(-3/4 : ℝ) := by
  have hp0 : (0 : ℝ)<p := by exact_mod_cast hp
  have hp1 : (1 : ℝ)≤p := by exact_mod_cast hp
  have hl2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hpow1 : 1≤(p : ℝ)^(1/4 : ℝ) := Real.one_le_rpow hp1 (by norm_num)
  have hpow2 : (2 : ℝ)^(1/4 : ℝ)≤2 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ)≤2) (by norm_num : (1/4 : ℝ)≤1)
  have hpow : (p+1 : ℝ)^(1/4 : ℝ) ≤ 2*(p : ℝ)^(1/4 : ℝ) := by
    calc
      _ ≤ (2*(p : ℝ))^(1/4 : ℝ) := Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
      _ = (2 : ℝ)^(1/4 : ℝ)*(p : ℝ)^(1/4 : ℝ) := Real.mul_rpow (by norm_num) hp0.le
      _ ≤ _ := mul_le_mul_of_nonneg_right hpow2 (by positivity)
  have hlog : Real.log (p+1 : ℝ) ≤ 8*(p : ℝ)^(1/4 : ℝ) := by
    have h := Real.log_le_rpow_div (by positivity : (0 : ℝ)≤p+1) (by norm_num : (0 : ℝ)<1/4)
    nlinarith
  have hcoef : 1+Real.log (p+1 : ℝ)/Real.log 2 ≤
      (1+8/Real.log 2)*(p : ℝ)^(1/4 : ℝ) := by
    have h := div_le_div_of_nonneg_right hlog hl2.le
    calc
      _ ≤ (p : ℝ)^(1/4 : ℝ)+8*(p : ℝ)^(1/4 : ℝ)/Real.log 2 := add_le_add hpow1 h
      _ = _ := by ring
  have he : (p : ℝ)^(1/4 : ℝ)/(p : ℝ) = (p : ℝ)^(-3/4 : ℝ) := by
    have h := Real.rpow_sub hp0 (1/4) 1
    norm_num at h
    simpa only [neg_div] using h.symm
  calc
    _ ≤ 3*Real.exp 4*((1+8/Real.log 2)*(p : ℝ)^(1/4 : ℝ))/p := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hcoef (by positivity)) hp0.le
    _ = primeCurrentBudgetConstant*((p : ℝ)^(1/4 : ℝ)/p) := by
      unfold primeCurrentBudgetConstant
      ring
    _ = _ := by rw [he]

lemma rawPrimeWinnerHarmonic_uniform_rpow_bound (p N : ℕ) :
    ‖rawPrimeWinnerHarmonic p N‖ ≤ primeCurrentBudgetConstant*(p : ℝ)^(-3/4 : ℝ) := by
  by_cases hp : p.Prime
  · exact ((rawPrimeWinnerHarmonic_norm_le_incidence p N).trans
      (primeWinnerLoserHarmonic_abs_tsum_log_bound p hp)).trans
        (prime_current_log_budget_le_rpow p hp.pos)
  · rw [rawPrimeWinnerHarmonic_zero_of_not_prime p N hp,norm_zero]
    exact mul_nonneg primeCurrentBudgetConstant_pos.le (Real.rpow_nonneg (Nat.cast_nonneg p) _)

lemma primeWinnerHarmonicLimit_uniform_rpow_bound (p : ℕ) :
    ‖primeWinnerHarmonicLimit p‖ ≤ primeCurrentBudgetConstant*(p : ℝ)^(-3/4 : ℝ) := by
  by_cases hp : p.Prime
  · exact ((primeWinnerHarmonicLimit_norm_le_incidence p).trans
      (primeWinnerLoserHarmonic_abs_tsum_log_bound p hp)).trans
        (prime_current_log_budget_le_rpow p hp.pos)
  · rw [primeWinnerHarmonicLimit_zero_of_not_prime p hp,norm_zero]
    exact mul_nonneg primeCurrentBudgetConstant_pos.le (Real.rpow_nonneg (Nat.cast_nonneg p) _)

lemma square_neg_three_quarters (p : ℕ) :
    ((p : ℝ)^(-3/4 : ℝ))^2=(p : ℝ)^(-3/2 : ℝ) := by
  rw [← Real.rpow_mul_natCast (Nat.cast_nonneg p)]
  norm_num

lemma harmonic_prime_current_l2_error_bound (N p : ℕ) :
    ‖(rawPrimeWinnerHarmonic p N-primeWinnerHarmonicLimit p)^2‖ ≤
      4*primeCurrentBudgetConstant^2*(p : ℝ)^(-3/2 : ℝ) := by
  have h := (norm_sub_le _ _).trans (add_le_add
    (rawPrimeWinnerHarmonic_uniform_rpow_bound p N)
    (primeWinnerHarmonicLimit_uniform_rpow_bound p))
  have hsq := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [norm_pow]
  apply hsq.trans_eq
  rw [← two_mul,mul_pow,mul_pow,square_neg_three_quarters]
  ring

lemma summable_primeWinnerHarmonicLimit_sq :
    Summable (fun p : ℕ => (primeWinnerHarmonicLimit p)^2) := by
  have hs := (Real.summable_nat_rpow.mpr (by norm_num : (-3/2 : ℝ)< -1)).mul_left
    (primeCurrentBudgetConstant^2)
  apply hs.of_norm_bounded
  intro p
  have h := pow_le_pow_left₀ (norm_nonneg _) (primeWinnerHarmonicLimit_uniform_rpow_bound p) 2
  rw [norm_pow]
  apply h.trans_eq
  rw [mul_pow,square_neg_three_quarters]

/-- The full vector converges in unnormalized l2, not only coordinatewise.
This does not imply convergence of the unweighted sum over prime labels. -/
theorem harmonic_prime_current_l2_convergence :
    Tendsto (fun N : ℕ => ∑' p : ℕ,
      (rawPrimeWinnerHarmonic p N-primeWinnerHarmonicLimit p)^2) atTop (𝓝 0) := by
  have hs := (Real.summable_nat_rpow.mpr (by norm_num : (-3/2 : ℝ)< -1)).mul_left
    (4*primeCurrentBudgetConstant^2)
  have ht (p : ℕ) : Tendsto (fun N =>
      (rawPrimeWinnerHarmonic p N-primeWinnerHarmonicLimit p)^2) atTop (𝓝 0) := by
    simpa only [sub_self,zero_pow (by norm_num : (2 : ℕ)≠0)] using
      ((rawPrimeWinnerHarmonic_tendsto p).sub_const (primeWinnerHarmonicLimit p)).pow 2
  have h := tendsto_tsum_of_dominated_convergence hs ht
    (Eventually.of_forall harmonic_prime_current_l2_error_bound)
  simpa only [tsum_zero] using h

#print axioms rawPrimeWinnerHarmonic_uniform_rpow_bound
#print axioms summable_primeWinnerHarmonicLimit_sq
#print axioms harmonic_prime_current_l2_convergence
end Erdos371
