import Submission.PrimeWinnerHarmonicLimits

/-! Exact harmonic prime-label flux. The divergence is nonnegative away from
label one, but the currents themselves can be negative. -/
namespace Erdos371
open Finset Filter FiniteInformation
open scoped Topology
set_option autoImplicit false

noncomputable def primeLabelIndicator (p n : ℕ) : ℝ :=
  if Nat.maxPrimeFac n=p then 1 else 0

lemma primeLabelIndicator_nonneg (p n : ℕ) : 0≤primeLabelIndicator p n := by
  unfold primeLabelIndicator
  split_ifs <;> norm_num

lemma primeWinnerLoser_sign_flux (p n : ℕ) :
    (if primeWinner n=p then factorSign n else 0) -
      (if primeLoser n=p then factorSign n else 0) =
      primeLabelIndicator p (n+1)-primeLabelIndicator p n := by
  unfold primeWinner primeLoser factorSign predicateSign primeLabelIndicator
  by_cases h : Nat.maxPrimeFac n<Nat.maxPrimeFac (n+1)
  · rw [if_pos h,max_eq_right h.le,min_eq_left h.le]
  · rw [if_neg h,max_eq_left (not_lt.mp h),min_eq_right (not_lt.mp h)]
    by_cases h1 : Nat.maxPrimeFac n=p <;> by_cases h2 : Nat.maxPrimeFac (n+1)=p <;>
      simp [h1,h2]

lemma primeWinnerLoser_harmonic_term_flux (p n : ℕ) :
    primeWinnerHarmonicTerm p n-primeLoserHarmonicTerm p n =
      (primeLabelIndicator p (n+1)-primeLabelIndicator p n)/n := by
  unfold primeWinnerHarmonicTerm primeLoserHarmonicTerm
  rw [← primeWinnerLoser_sign_flux,sub_div]
  simp only [ite_div,zero_div]

lemma reciprocal_discrete_derivative (a : ℕ → ℝ) (M : ℕ) :
    (∑ n ∈ range (M+2), (a (n+1)-a n)/(n : ℝ)) =
      a (M+2)/(M+1 : ℝ)-a 1+
        ∑ n ∈ range M, a (n+2)*(1/(n+1 : ℝ)-1/(n+2 : ℝ)) := by
  induction M with
  | zero => norm_num [sum_range_succ]
  | succ M ih =>
    rw [show M+1+2=(M+2)+1 by omega,sum_range_succ,ih,sum_range_succ]
    push_cast
    simp only [Nat.add_assoc]
    ring

/-- Finite weighted conservation, including the terminal contribution. -/
theorem rawPrimeHarmonic_flux (p M : ℕ) :
    rawPrimeWinnerHarmonic p (M+2)-rawPrimeLoserHarmonic p (M+2) =
      primeLabelIndicator p (M+2)/(M+1 : ℝ)-primeLabelIndicator p 1+
        ∑ n ∈ range M, primeLabelIndicator p (n+2)*(1/(n+1 : ℝ)-1/(n+2 : ℝ)) := by
  unfold rawPrimeWinnerHarmonic rawPrimeLoserHarmonic
  rw [← sum_sub_distrib]
  simp_rw [primeWinnerLoser_harmonic_term_flux]
  exact reciprocal_discrete_derivative (primeLabelIndicator p) M

lemma rawPrimeHarmonic_flux_nonneg (p N : ℕ) (hp : 2≤p) :
    0≤rawPrimeWinnerHarmonic p N-rawPrimeLoserHarmonic p N := by
  rcases N with _|_|M
  · simp [rawPrimeWinnerHarmonic,rawPrimeLoserHarmonic]
  · simp [rawPrimeWinnerHarmonic,rawPrimeLoserHarmonic,primeWinnerHarmonicTerm,primeLoserHarmonicTerm]
  · rw [rawPrimeHarmonic_flux]
    have he : primeLabelIndicator p 1=0 := by simp [primeLabelIndicator,show 1≠p by omega]
    rw [he,sub_zero]
    apply add_nonneg
    · exact div_nonneg (primeLabelIndicator_nonneg p _) (by positivity)
    · apply sum_nonneg
      intro n hn
      apply mul_nonneg (primeLabelIndicator_nonneg p _)
      exact sub_nonneg.mpr (one_div_le_one_div_of_le (by positivity) (by linarith))

/-- The same nonnegative divergence holds for the absolutely convergent,
fixed-prime infinite currents. This is not positivity of either current. -/
theorem primeHarmonicLimit_flux_nonneg (p : ℕ) (hp : 2≤p) :
    0≤primeWinnerHarmonicLimit p-primeLoserHarmonicLimit p :=
  ge_of_tendsto ((rawPrimeWinnerHarmonic_tendsto p).sub (rawPrimeLoserHarmonic_tendsto p))
    (Eventually.of_forall (fun N => rawPrimeHarmonic_flux_nonneg p N hp))

/-- A small exact obstruction to positivity of individual harmonic currents. -/
theorem rawPrimeWinnerHarmonic_7_15 : rawPrimeWinnerHarmonic 7 15 = -1/21 := by
  have hq : (∑ n ∈ range 15, if primeWinner n=7 then
      (if Nat.maxPrimeFac n<Nat.maxPrimeFac (n+1) then (1 : ℚ) else -1)/(n : ℚ) else 0) = -1/21 := by
    decide +kernel
  have hr := congrArg (fun x : ℚ => (x : ℝ)) hq
  simp only [Rat.cast_sum,apply_ite,Rat.cast_div,Rat.cast_natCast,Rat.cast_zero,Rat.cast_one,Rat.cast_neg] at hr
  simpa only [rawPrimeWinnerHarmonic,primeWinnerHarmonicTerm,factorSign,predicateSign] using hr

theorem not_rawPrimeWinnerHarmonic_nonneg :
    ¬∀ p N : ℕ, 0≤rawPrimeWinnerHarmonic p N := by
  intro h
  have hh := h 7 15
  rw [rawPrimeWinnerHarmonic_7_15] at hh
  norm_num at hh

#print axioms rawPrimeHarmonic_flux
#print axioms primeHarmonicLimit_flux_nonneg
#print axioms not_rawPrimeWinnerHarmonic_nonneg
end Erdos371
