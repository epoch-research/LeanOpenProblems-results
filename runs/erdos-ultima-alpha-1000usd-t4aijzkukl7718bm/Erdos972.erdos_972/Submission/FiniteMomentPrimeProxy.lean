import Submission.CriticalNonlinearPrimeProxy

/-! A smaller sufficient moment range for weighted prime detection.
No divergence estimate for this detector at prescribed irrational slopes is asserted. -/
namespace Erdos972FiniteMomentPrimeProxy

open Finset Filter
open scoped Topology
open Erdos972CriticalNonlinearPrimeProxy Erdos972NonlinearPrimeProxy
open Erdos972SmoothMangoldt Erdos972SmoothMangoldtPositive Erdos972PrimePowerError

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable def truncatedProxy (J n : ℕ) : ℝ :=
  if 1 < n then
    ∑ j ∈ range J, Real.exp (-(2:ℝ)*Real.log n)*(expDivisorSum 2 n)^j
  else 0

lemma truncatedProxy_nonneg (J n : ℕ) : 0 ≤ truncatedProxy J n := by
  unfold truncatedProxy
  split_ifs
  · exact sum_nonneg fun j _ => mul_nonneg (Real.exp_nonneg _)
      (pow_nonneg (expDivisorSum_nonneg (by norm_num) n) j)
  · exact le_rfl

lemma truncatedProxy_le (J n : ℕ) : truncatedProxy J n ≤ primeProxy 2 n := by
  by_cases hn : 1 < n
  · rw [truncatedProxy, if_pos hn]
    have hs := hasSum_primeProxy (by norm_num : (0:ℝ) ≤ 2) hn
    exact (hs.summable.sum_le_tsum (range J) (fun j _ =>
      mul_nonneg (Real.exp_nonneg _) (pow_nonneg (expDivisorSum_nonneg (by norm_num) n) j))).trans_eq
        hs.tsum_eq
  · simp only [truncatedProxy, primeProxy, if_neg hn, le_refl]

lemma truncatedProxy_prime_eq {q : ℕ} (hq : q.Prime) (J : ℕ) :
    truncatedProxy J q = 1 - (1 - ((q:ℝ)^2)⁻¹)^J := by
  have he : expDivisorSum 2 q = 1 - ((q:ℝ)^2)⁻¹ := by
    simpa only [pow_one, exp_neg_two_log hq.pos] using
      expDivisorSum_prime_pow 2 hq (by decide : 0 < 1)
  rw [truncatedProxy, if_pos hq.one_lt, exp_neg_two_log hq.pos, he, ← mul_sum]
  have hh := geom_sum_mul_neg (1 - ((q:ℝ)^2)⁻¹) J
  simp only [sub_sub_cancel] at hh
  nlinarith only [hh]

lemma damped_power_bound {x : ℝ} (_hx0 : 0 ≤ x) (hx1 : x ≤ 1) (J : ℕ) :
    (1 + (J:ℝ)*x)*(1-x)^J ≤ 1 := by
  induction J with
  | zero => simp
  | succ J ih =>
    have hstep : (1 + ((J+1:ℕ):ℝ)*x)*(1-x) ≤ 1 + (J:ℝ)*x := by
      push_cast
      nlinarith [mul_nonneg (show (0:ℝ) ≤ J+1 by positivity) (sq_nonneg x)]
    calc
      _ = ((1 + ((J+1:ℕ):ℝ)*x)*(1-x))*(1-x)^J := by rw [pow_succ]; ring
      _ ≤ (1 + (J:ℝ)*x)*(1-x)^J :=
        mul_le_mul_of_nonneg_right hstep (pow_nonneg (sub_nonneg.mpr hx1) J)
      _ ≤ 1 := ih

lemma geometric_loss_lower {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (J : ℕ) :
    (J:ℝ)*x/(1+(J:ℝ)*x) ≤ 1-(1-x)^J := by
  apply (div_le_iff₀ (show (0:ℝ) < 1+(J:ℝ)*x by positivity)).mpr
  nlinarith only [damped_power_bound hx0 hx1 J]

/-- A lower bound for every moment budget, not only budgets comparable to q^2. -/
theorem truncatedProxy_prime_lower {q : ℕ} (hq : q.Prime) (J : ℕ) :
    (J:ℝ)/((q:ℝ)^2 + J) ≤ truncatedProxy J q := by
  have hqR : (0:ℝ) < q := Nat.cast_pos.mpr hq.pos
  have hq1 : (1:ℝ) ≤ q := by exact_mod_cast hq.one_le
  have hsq : (1:ℝ) ≤ (q:ℝ)^2 := by nlinarith
  have hx1 : ((q:ℝ)^2)⁻¹ ≤ 1 := (inv_le_one₀ (by positivity)).mpr hsq
  rw [truncatedProxy_prime_eq hq]
  have hh := geometric_loss_lower (inv_nonneg.mpr (sq_nonneg (q:ℝ))) hx1 J
  have heq : (J:ℝ)*((q:ℝ)^2)⁻¹/(1+(J:ℝ)*((q:ℝ)^2)⁻¹) =
      (J:ℝ)/((q:ℝ)^2+J) := by
    have hd : (0:ℝ) < (q:ℝ)^2 + J := by positivity
    field_simp
  rwa [heq] at hh

lemma truncatedProxy_prime_upper {q : ℕ} (hq : q.Prime) (J : ℕ) :
    truncatedProxy J q ≤ (J:ℝ)/(q:ℝ)^2 := by
  simpa only [truncatedProxy, if_pos hq.one_lt] using prime_truncated_proxy_bound_two hq J

/-- Below q^2 moments, the prime contribution is within a factor two of J/q^2. -/
theorem truncatedProxy_prime_comparison {q : ℕ} (hq : q.Prime) {J : ℕ}
    (hJ : J ≤ q^2) :
    (J:ℝ)/(2*(q:ℝ)^2) ≤ truncatedProxy J q ∧
      truncatedProxy J q ≤ (J:ℝ)/(q:ℝ)^2 := by
  refine ⟨?_, truncatedProxy_prime_upper hq J⟩
  have hJR : (J:ℝ) ≤ (q:ℝ)^2 := by exact_mod_cast hJ
  have hqR : (0:ℝ) < q := Nat.cast_pos.mpr hq.pos
  apply le_trans _ (truncatedProxy_prime_lower hq J)
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg J) (by positivity) (by linarith)

/-- This budget is q times its integer base-two logarithm, not q squared. -/
def logarithmicBudget (q : ℕ) : ℕ := q * Nat.log 2 q

lemma logarithmicBudget_le_sq (q : ℕ) : logarithmicBudget q ≤ q^2 := by
  simpa only [logarithmicBudget, pow_two] using Nat.mul_le_mul_left q (Nat.log_le_self 2 q)

/-- The logarithmic moment budget detects primes with weight comparable to log(q)/q. -/
theorem logarithmicBudget_prime_bounds {q : ℕ} (hq : q.Prime) :
    ((Nat.log 2 q : ℕ):ℝ)/(2*q) ≤ truncatedProxy (logarithmicBudget q) q ∧
      truncatedProxy (logarithmicBudget q) q ≤ ((Nat.log 2 q : ℕ):ℝ)/q := by
  have hh := truncatedProxy_prime_comparison hq (logarithmicBudget_le_sq q)
  have hqR : (q:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero
  have he1 : ((logarithmicBudget q:ℕ):ℝ)/(2*(q:ℝ)^2) =
      ((Nat.log 2 q : ℕ):ℝ)/(2*q) := by
    simp only [logarithmicBudget, Nat.cast_mul]
    field_simp
  have he2 : ((logarithmicBudget q:ℕ):ℝ)/(q:ℝ)^2 =
      ((Nat.log 2 q : ℕ):ℝ)/q := by
    simp only [logarithmicBudget, Nat.cast_mul]
    field_simp
  simpa only [he1, he2] using hh

/-- Removing genuine-prime outputs leaves a uniformly dominated composite term,
for an arbitrary output-dependent budget J. -/
noncomputable def truncatedCompositeError (J : ℕ → ℕ) (α : ℝ) (p : ℕ) : ℝ :=
  if p.Prime ∧ ¬ (floorMul α p).Prime then
    truncatedProxy (J (floorMul α p)) (floorMul α p) else 0

lemma truncatedCompositeError_bounds (J : ℕ → ℕ) (α : ℝ) (p : ℕ) :
    0 ≤ truncatedCompositeError J α p ∧
      truncatedCompositeError J α p ≤ compositeProxyTwo (floorMul α p) := by
  classical
  unfold truncatedCompositeError
  split_ifs with h
  · rw [compositeProxyTwo, if_neg h.2]
    exact ⟨truncatedProxy_nonneg _ _, truncatedProxy_le _ _⟩
  · exact ⟨le_rfl, compositeProxyTwo_nonneg _⟩

/-- Composite error remains summable even when the moment budget grows with the output. -/
theorem summable_truncatedCompositeError (J : ℕ → ℕ) {α : ℝ} (hα : 1 ≤ α) :
    Summable (truncatedCompositeError J α) := by
  have hs := summable_compositeProxyTwo.comp_injective (floorMul_strictMono hα).injective
  exact hs.of_nonneg_of_le (fun p => (truncatedCompositeError_bounds J α p).1)
    (fun p => (truncatedCompositeError_bounds J α p).2)

#print axioms truncatedProxy_prime_lower
#print axioms truncatedProxy_prime_comparison
#print axioms logarithmicBudget_prime_bounds
#print axioms summable_truncatedCompositeError

end Erdos972FiniteMomentPrimeProxy
