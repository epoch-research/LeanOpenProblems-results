import Submission.UniformClosedFibers
import Submission.ThousandPoolStrictGain

/-!
# The strict thousand-band gain at closed outputs with small radicals

The existing general padding transfer preserves every strictly smaller
exponent from the refined smooth-prime count. The radical order and the
output lower bound can be prescribed independently. No exponent approaching
one, or lower bound for large-overlap pairs, is asserted here.
-/

open Nat Filter
open scoped Classical BigOperators

namespace Erdos821.ClosedPadding
open AnalyticSieve HigherDivisors
set_option maxHeartbeats 3000000

lemma closed_fibers_of_single_log_smooth_count (t b C : ℕ) (hbt : b < t)
    (H : ∀ᶠ m : ℕ in atTop,
      (independentN t m : ℝ) ≤ (C : ℝ)*m*
        ((smoothPrimePool (independentN t m) (independentN b m)).card : ℝ))
    (γ : ℝ) (hγ : 0 ≤ γ) (hγb : γ < 1-(b : ℝ)/t) (r N : ℕ) :
    ∃ n : ℕ, N < n ∧ (n : ℝ)^γ < g n ∧
      RadicalLift.radical n^r ≤ n ∧ totient (RadicalLift.radical n) ∣ n := by
  apply closed_fibers_of_eventual_polynomial_count (64*t) (64*b) 1 C 1
    (Nat.mul_lt_mul_of_pos_left hbt (by decide)) ?_ γ hγ ?_ r N
  · filter_upwards [H] with m hm
    refine ⟨smoothPrimePool (independentN t m) (independentN b m), ?_, ?_⟩
    · intro p hp
      obtain ⟨hp, hs⟩ := Finset.mem_filter.mp hp
      obtain ⟨hN, hpr⟩ := Nat.mem_primesBelow.mp hp
      refine ⟨hpr, ?_, ?_⟩
      · change p ≤ independentN t m
        omega
      · simpa only [one_mul] using hs
    · have hh : independentN t m ≤ C*m*
          (smoothPrimePool (independentN t m) (independentN b m)).card := by
        exact_mod_cast hm
      exact hh.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left C (by simp)))
  · simpa only [Nat.cast_mul, Nat.cast_ofNat,
      mul_div_mul_left _ _ (by norm_num : (64 : ℝ) ≠ 0)] using hγb

/-- The refined exponent survives at closed outputs whose radicals are
below every prescribed root. The one natural parameter K is fixed before
all exponents, radical orders, and output lower bounds are requested. -/
theorem exists_thousand_pool_closed_strict_gain :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ γ : ℝ, 0 ≤ γ →
      γ < 406887/666667 + 1/(40000020*(K : ℝ)) → ∀ r N : ℕ,
      ∃ n : ℕ, N < n ∧ (n : ℝ)^γ < g n ∧
        RadicalLift.radical n^r ≤ n ∧ totient (RadicalLift.radical n) ∣ n := by
  obtain ⟨C, hC, HC⟩ := exists_thousand_pool_smooth_prime_count
  obtain ⟨K, C', hK, _hC', _hratio, Hsmall⟩ :=
    exists_smaller_cutoff_single_log_count 40000020 15586800 C
      (by decide) (by decide) (by decide) hC HC
  refine ⟨K, hK, ?_⟩
  intro γ hγ hγb r N
  apply closed_fibers_of_single_log_smooth_count (40000020*K) (15586800*K-1)
    C' (by omega) Hsmall γ hγ ?_ r N
  have hKR : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hsub : ((15586800*K-1 : ℕ) : ℝ) = 15586800*(K : ℝ)-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 15586800*K)]
    push_cast
    rfl
  have he : 1-((15586800*K-1 : ℕ) : ℝ)/((40000020*K : ℕ) : ℝ) =
      406887/666667+1/(40000020*(K : ℝ)) := by
    rw [hsub]
    push_cast
    field_simp
    ring
  rwa [he]

/-- Infinitely many closed, small-radical outputs attain the previous exact
rational endpoint. This is still one fixed multiplicity exponent. -/
theorem infinite_thousand_pool_closed_endpoint (r : ℕ) :
    {n : ℕ | (n : ℝ)^(406887/666667 : ℝ) < g n ∧
      RadicalLift.radical n^r ≤ n ∧ totient (RadicalLift.radical n) ∣ n}.Infinite := by
  obtain ⟨K, hK, H⟩ := exists_thousand_pool_closed_strict_gain
  have hKR : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hpos : (0 : ℝ) < 1/(40000020*(K : ℝ)) := by positivity
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨n, hn, hg, hr, hc⟩ := H (406887/666667) (by norm_num)
    (by linarith) r N
  exact ⟨n, ⟨hg, hr, hc⟩, hn⟩

/-- One exponent strictly beyond the rational endpoint works for every
fixed radical order, still without providing exponents tending to one. -/
theorem exists_closed_exponent_above_thousand_pool :
    ∃ γ : ℝ, 406887/666667 < γ ∧ ∀ r : ℕ,
      {n : ℕ | (n : ℝ)^γ < g n ∧ RadicalLift.radical n^r ≤ n ∧
        totient (RadicalLift.radical n) ∣ n}.Infinite := by
  obtain ⟨K, hK, H⟩ := exists_thousand_pool_closed_strict_gain
  have hKR : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hpos : (0 : ℝ) < 1/(40000020*(K : ℝ)) := by positivity
  let γ : ℝ := 406887/666667+(1/(40000020*(K : ℝ)))/2
  have hγ : 0 ≤ γ := by dsimp [γ]; positivity
  have hγb : γ < 406887/666667+1/(40000020*(K : ℝ)) := by dsimp [γ]; linarith
  refine ⟨γ, by dsimp [γ]; linarith, ?_⟩
  intro r
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨n, hn, hg, hr, hc⟩ := H γ hγ hγb r N
  exact ⟨n, ⟨hg, hr, hc⟩, hn⟩

end Erdos821.ClosedPadding
