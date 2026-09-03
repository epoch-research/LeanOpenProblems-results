import Submission.FifthBound

/-!
# A root-free equivalent of the all-exponent squarefree-gap conjecture

The all-positive-exponents statement is equivalent to the following purely
natural-number interval property: for each fixed `k`, every sufficiently large
`H` has a squarefree integer in `(x,x+H]` for every `x ≤ H^k`.

This file proves the equivalence, not the interval property for every `k`.
-/

open Filter Real

namespace SquarefreeGaps

/-- A uniform squarefree interval bound with a fixed polynomial horizon. -/
def PowerHorizon (k : ℕ) : Prop :=
  ∃ H₀ : ℕ, ∀ H ≥ H₀, ∀ x : ℕ, x ≤ H ^ k →
    ∃ n : ℕ, x < n ∧ n ≤ x + H ∧ Squarefree n

/-- All real positive exponents give every natural polynomial horizon.
Small starting points are handled separately by one fixed prime. -/
theorem powerHorizon_of_all_gap (h : ∀ ε > (0 : ℝ), GapBound ε) (k : ℕ) :
    PowerHorizon k := by
  have hε : (0 : ℝ) < ((k + 1 : ℕ) : ℝ)⁻¹ := by positivity
  have hunit := all_gap_iff_unit_intervals.mp h _ hε
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp hunit
  obtain ⟨p, hp₀, hp⟩ := Nat.exists_infinite_primes x₀
  refine ⟨max 1 p, ?_⟩
  intro H hH x hx
  have hHpos : 0 < H := by omega
  by_cases hxlarge : x₀ ≤ x
  · obtain ⟨n, hsq, hxn, hn⟩ := hx₀ x hxlarge
    have hxp : (x : ℝ) ≤ (H : ℝ) ^ (k + 1) := by
      exact_mod_cast hx.trans (Nat.pow_le_pow_right hHpos (Nat.le_succ k))
    have hroot : (x : ℝ) ^ ((k + 1 : ℕ) : ℝ)⁻¹ ≤ (H : ℝ) := by
      calc
        (x : ℝ) ^ ((k + 1 : ℕ) : ℝ)⁻¹ ≤
            ((H : ℝ) ^ (k + 1)) ^ ((k + 1 : ℕ) : ℝ)⁻¹ :=
          Real.rpow_le_rpow (Nat.cast_nonneg x) hxp hε.le
        _ = (H : ℝ) := Real.pow_rpow_inv_natCast (Nat.cast_nonneg H) (by omega)
    have hnH : (n : ℝ) ≤ (x : ℝ) + H := by linarith [hn.trans hroot]
    exact ⟨n, hxn, by exact_mod_cast hnH, hsq⟩
  · exact ⟨p, by omega, by omega, hp.squarefree⟩

/-- Natural polynomial horizons imply all real positive exponents. -/
theorem all_gap_of_powerHorizon (h : ∀ k : ℕ, PowerHorizon k) :
    ∀ ε > (0 : ℝ), GapBound ε := by
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_gt (max 1 ε⁻¹)
  have hkR : (0 : ℝ) < k := by linarith [le_max_left (1 : ℝ) ε⁻¹]
  have hkpos : 0 < k := by exact_mod_cast hkR
  have hratio : (1 : ℝ) / k ≤ ε := by
    rw [one_div]
    apply (inv_le_iff_one_le_mul₀ hkR).mpr
    have hmul := (inv_lt_iff_one_lt_mul₀ hε).mp ((le_max_right (1 : ℝ) ε⁻¹).trans_lt hk)
    nlinarith
  apply gap_of_interval
  apply intervalBound_mono hratio
  simpa only [Nat.cast_one] using
    (intervalBound_of_polynomial_intervals (a := k) (b := 1) (C := 1) hkpos (by decide)
      (by simpa only [PowerHorizon, one_mul, pow_one] using h k))

/-- Exact equivalence with the conjecture, with no unproved input in either direction. -/
theorem all_gap_iff_power_horizons :
    (∀ ε > (0 : ℝ), GapBound ε) ↔ ∀ k : ℕ, PowerHorizon k :=
  ⟨powerHorizon_of_all_gap, all_gap_of_powerHorizon⟩

#print axioms all_gap_iff_power_horizons

end SquarefreeGaps
