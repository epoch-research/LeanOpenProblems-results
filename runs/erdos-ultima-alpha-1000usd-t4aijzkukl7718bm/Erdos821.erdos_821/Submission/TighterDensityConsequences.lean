import Submission.TighterWideDensity
import Submission.WideBlockReciprocal
import Submission.PolylogSpectrumInterval

/-!
# Consequences of the stronger fixed-ratio prime count

These strengthen the proved reciprocal-divergence and restricted-input
ranges. The smoothness ratio is still bounded away from zero.
-/
open Nat Filter
open scoped Classical BigOperators
namespace Erdos821
open AnalyticSieve HigherDivisors
set_option maxHeartbeats 3000000

theorem tight_wide_prime_reciprocal_divergence :
    ¬Summable ((rationalSmoothShiftedPrimes 40000019 19175170).indicator
      (fun p : ℕ => 1/(p : ℝ))) := by
  obtain ⟨C,_hC,H⟩ := exists_tight_wide_smooth_prime_count
  exact not_summable_relative_of_single_log_count 40000020 19175170 C (by decide) H

lemma tight_wide_eventual_polynomial_count :
    ∃ C : ℕ, ∀ᶠ m : ℕ in atTop, ∃ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ p ≤ 2^((64*40000020)*m) ∧
        p-1 ∈ Nat.smoothNumbers (1*2^((64*19175170)*m))) ∧
      2^((64*40000020)*m) ≤ C*(m+1)^1*P.card := by
  obtain ⟨C,_hC,H⟩ := exists_tight_wide_smooth_prime_count
  refine ⟨C,?_⟩
  filter_upwards [H] with m hm
  refine ⟨smoothPrimePool (independentN 40000020 m) (independentN 19175170 m),?_,?_⟩
  · intro p hp
    obtain ⟨hp,hs⟩ := Finset.mem_filter.mp hp
    obtain ⟨hN,hpr⟩ := Nat.mem_primesBelow.mp hp
    refine ⟨hpr,?_,?_⟩
    · change p ≤ independentN 40000020 m
      omega
    · simpa only [one_mul] using hs
  · have hh : independentN 40000020 m ≤
        C*m*(smoothPrimePool (independentN 40000020 m) (independentN 19175170 m)).card := by
      exact_mod_cast hm
    exact hh.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left C (by simp)))

theorem polylog_critical_exponent_tight_wide_interval (κ : ℝ) (hκ : 1 < κ)
    (hκb : κ ≤ 4000002/1917517) :
    sSup {γ : ℝ | {n : ℕ | (gPolylog κ n : ℝ) > (n : ℝ)^γ}.Infinite} = 1-1/κ := by
  obtain ⟨C,H⟩ := tight_wide_eventual_polynomial_count
  apply polylog_critical_exponent_of_polynomial_count (64*40000020) (64*19175170)
    1 C 1 (by omega) H κ hκ
  norm_num
  nlinarith only [hκb]

theorem infinite_gPolylog_gt_tight_wide_interval (κ γ : ℝ) (hκ : 1 < κ)
    (hκb : κ ≤ 4000002/1917517) (hγ : γ < 1-1/κ) :
    {n : ℕ | (gPolylog κ n : ℝ) > (n : ℝ)^γ}.Infinite := by
  obtain ⟨C,H⟩ := tight_wide_eventual_polynomial_count
  apply infinite_gPolylog_gt_of_polynomial_count (64*40000020) (64*19175170)
    1 C 1 (by omega) H κ γ hκ ?_ hγ
  norm_num
  nlinarith only [hκb]

theorem tight_wide_polylog_input_fibers (γ : ℝ) (hγ : γ < 2082485/4000002) (N : ℕ) :
    ∃ (n : ℕ) (F : Finset ℕ), N < n ∧ (n : ℝ)^γ < F.card ∧
      ∀ m ∈ F, Squarefree m ∧ totient m=n ∧
        ∀ p ∈ m.primeFactors,
          (p : ℝ) ≤ (4*Real.log (n : ℝ))^(4000002/1917517 : ℝ) := by
  obtain ⟨C,H⟩ := tight_wide_eventual_polynomial_count
  have hh := polylog_input_fibers_of_eventual_polynomial_count (64*40000020)
    (64*19175170) 1 C 1 (by norm_num) (by norm_num) H γ (by norm_num; exact hγ) N
  norm_num only [Nat.cast_mul,Nat.cast_ofNat] at hh
  exact hh

end Erdos821
