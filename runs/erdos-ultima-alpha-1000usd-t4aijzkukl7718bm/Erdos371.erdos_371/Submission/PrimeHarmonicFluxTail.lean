import Submission.DyadicSeriesTools
import Submission.PrimeWinnerHarmonicFlux

/-! Uniform prime-weighted square tails for the harmonic conservation
correction. These are not bounds for either current separately. -/
namespace Erdos371
open Finset Filter
open scoped Topology
set_option autoImplicit false

lemma harmonic_derivative_prefix_bound_of_cutoff (a : ℕ → ℝ) (B N : ℕ)
    (ha : ∀ n, 0≤a n ∧ a n≤1) (hB : 0<B) (hz : ∀ n, n≤B → a n=0) :
    |∑ n ∈ range N, (a (n+1)-a n)/(n : ℝ)|≤1/(B : ℝ) := by
  have hzero (M : ℕ) (hM : M≤B) :
      (∑ n ∈ range M, (a (n+1)-a n)/(n : ℝ))=0 := by
    apply sum_eq_zero
    intro n hn
    have hn' := mem_range.mp hn
    rw [hz (n+1) (by omega),hz n (by omega),sub_self,zero_div]
  by_cases hN : N≤B
  · rw [hzero N hN,abs_zero]
    positivity
  · have hBN : B≤N := (not_le.mp hN).le
    rw [← sum_range_add_sum_Ico _ hBN,hzero B le_rfl,zero_add]
    exact reciprocal_derivative_Ico_bound a ha B N hB hBN

lemma finite_primeLabelIndicator_sum (S : Finset ℕ) (n : ℕ) :
    (∑ p ∈ S, primeLabelIndicator p n) = if Nat.maxPrimeFac n ∈ S then 1 else 0 := by
  classical
  simp [primeLabelIndicator,eq_comm]

lemma finite_primeHarmonic_flux_sum (S : Finset ℕ) (N : ℕ) :
    (∑ p ∈ S, (rawPrimeWinnerHarmonic p N-rawPrimeLoserHarmonic p N)) =
      ∑ n ∈ range N, ((∑ p ∈ S, primeLabelIndicator p (n+1))-
        (∑ p ∈ S, primeLabelIndicator p n))/(n : ℝ) := by
  unfold rawPrimeWinnerHarmonic rawPrimeLoserHarmonic
  simp_rw [← sum_sub_distrib,primeWinnerLoser_harmonic_term_flux]
  rw [sum_comm]
  apply sum_congr rfl
  intro n hn
  rw [sum_div]

/-- The nonnegative conservation correction has at most 1/B total mass on
any finite set of labels larger than B, uniformly in the endpoint. -/
theorem finite_primeHarmonic_flux_tail_bound (S : Finset ℕ) (B N : ℕ)
    (hB : 0<B) (hS : ∀ p ∈ S, B<p) :
    (∑ p ∈ S, (rawPrimeWinnerHarmonic p N-rawPrimeLoserHarmonic p N)) ≤
      1/(B : ℝ) := by
  classical
  let a (n : ℕ) : ℝ := ∑ p ∈ S, primeLabelIndicator p n
  have ha (n : ℕ) : 0≤a n ∧ a n≤1 := by
    dsimp [a]
    rw [finite_primeLabelIndicator_sum]
    split_ifs <;> norm_num
  have hz (n : ℕ) (hn : n≤B) : a n=0 := by
    dsimp [a]
    rw [finite_primeLabelIndicator_sum,if_neg]
    intro h
    have hp := hS _ h
    have hp' := Nat.maxPrimeFac_le (n := n)
    omega
  rw [finite_primeHarmonic_flux_sum]
  exact (le_abs_self _).trans (harmonic_derivative_prefix_bound_of_cutoff a B N ha hB hz)

lemma primeHarmonic_flux_mul_label_le_two (p N : ℕ) (hp : 2≤p) :
    (p : ℝ)*(rawPrimeWinnerHarmonic p N-rawPrimeLoserHarmonic p N)≤2 := by
  have hb := finite_primeHarmonic_flux_tail_bound {p} (p-1) N (by omega)
    (by intro q hq; simp only [mem_singleton] at hq; omega)
  simp only [sum_singleton] at hb
  have hp' : (0 : ℝ)<(p-1 : ℕ) := by exact_mod_cast (by omega : 0<p-1)
  have hc : (p : ℝ)≤2*((p-1 : ℕ) : ℝ) := by
    exact_mod_cast (show p≤2*(p-1) by omega)
  calc
    _ ≤ (p : ℝ)*(1/((p-1 : ℕ) : ℝ)) := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg p)
    _ ≤ 2 := by rw [mul_one_div]; exact (div_le_iff₀ hp').mpr hc

/-- Uniform square-tail tightness with the critical prime weight for the
WINNER-MINUS-LOSER correction, not for the winner or loser currents. -/
theorem finite_primeHarmonic_flux_weighted_square_tail (S : Finset ℕ) (B N : ℕ)
    (hB : 0<B) (hS : ∀ p ∈ S, B<p) :
    (∑ p ∈ S, (p : ℝ)*(rawPrimeWinnerHarmonic p N-rawPrimeLoserHarmonic p N)^2) ≤
      2/(B : ℝ) := by
  have hterm (p : ℕ) (hp : p ∈ S) :
      (p : ℝ)*(rawPrimeWinnerHarmonic p N-rawPrimeLoserHarmonic p N)^2 ≤
        2*(rawPrimeWinnerHarmonic p N-rawPrimeLoserHarmonic p N) := by
    have hp2 : 2≤p := by have := hS p hp; omega
    have hn := rawPrimeHarmonic_flux_nonneg p N hp2
    have hh := mul_le_mul_of_nonneg_right (primeHarmonic_flux_mul_label_le_two p N hp2) hn
    nlinarith
  calc
    _ ≤ ∑ p ∈ S, 2*(rawPrimeWinnerHarmonic p N-rawPrimeLoserHarmonic p N) := sum_le_sum hterm
    _ = 2*∑ p ∈ S, (rawPrimeWinnerHarmonic p N-rawPrimeLoserHarmonic p N) := (mul_sum ..).symm
    _ ≤ 2*(1/(B : ℝ)) := mul_le_mul_of_nonneg_left
      (finite_primeHarmonic_flux_tail_bound S B N hB hS) (by norm_num)
    _ = _ := by ring

lemma finite_primeHarmonic_limit_flux_weighted_square_tail (S : Finset ℕ) (B : ℕ)
    (hB : 0<B) (hS : ∀ p ∈ S, B<p) :
    (∑ p ∈ S, (p : ℝ)*(primeWinnerHarmonicLimit p-primeLoserHarmonicLimit p)^2) ≤
      2/(B : ℝ) := by
  have ht := tendsto_finset_sum S (fun p _ =>
    (((rawPrimeWinnerHarmonic_tendsto p).sub (rawPrimeLoserHarmonic_tendsto p)).pow 2).const_mul (p : ℝ))
  exact le_of_tendsto ht (Eventually.of_forall
    (fun N => finite_primeHarmonic_flux_weighted_square_tail S B N hB hS))

/-- Even the error from the limiting conservation correction has uniformly
small weighted square tails. This still does not control either current. -/
theorem finite_primeHarmonic_flux_error_weighted_square_tail (S : Finset ℕ) (B N : ℕ)
    (hB : 0<B) (hS : ∀ p ∈ S, B<p) :
    (∑ p ∈ S, (p : ℝ)*((rawPrimeWinnerHarmonic p N-rawPrimeLoserHarmonic p N)-
      (primeWinnerHarmonicLimit p-primeLoserHarmonicLimit p))^2) ≤ 8/(B : ℝ) := by
  have hterm (p : ℕ) (_hp : p ∈ S) :
      (p : ℝ)*((rawPrimeWinnerHarmonic p N-rawPrimeLoserHarmonic p N)-
        (primeWinnerHarmonicLimit p-primeLoserHarmonicLimit p))^2 ≤
      2*((p : ℝ)*(rawPrimeWinnerHarmonic p N-rawPrimeLoserHarmonic p N)^2)+
        2*((p : ℝ)*(primeWinnerHarmonicLimit p-primeLoserHarmonicLimit p)^2) := by
    have hsq (x y : ℝ) : (x-y)^2≤2*x^2+2*y^2 := by nlinarith [sq_nonneg (x+y)]
    have h := mul_le_mul_of_nonneg_left
      (hsq (rawPrimeWinnerHarmonic p N-rawPrimeLoserHarmonic p N)
        (primeWinnerHarmonicLimit p-primeLoserHarmonicLimit p)) (Nat.cast_nonneg (α := ℝ) p)
    nlinarith
  have hh := sum_le_sum hterm
  rw [sum_add_distrib,← mul_sum,← mul_sum] at hh
  have h₁ := finite_primeHarmonic_flux_weighted_square_tail S B N hB hS
  have h₂ := finite_primeHarmonic_limit_flux_weighted_square_tail S B hB hS
  have hb := add_le_add (mul_le_mul_of_nonneg_left h₁ (by norm_num : (0 : ℝ)≤2))
    (mul_le_mul_of_nonneg_left h₂ (by norm_num : (0 : ℝ)≤2))
  exact hh.trans (hb.trans_eq (by ring))

#print axioms finite_primeHarmonic_flux_tail_bound
#print axioms finite_primeHarmonic_flux_weighted_square_tail
#print axioms finite_primeHarmonic_flux_error_weighted_square_tail
end Erdos371
