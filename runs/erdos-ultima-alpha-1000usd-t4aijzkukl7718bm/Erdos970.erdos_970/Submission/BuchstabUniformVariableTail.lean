import Submission.BuchstabVariableTail

/-! The finite tail proofs have a prime threshold independent of the terminal
cutoff. This exposes that uniformity explicitly; both the terminal allowance
and all finite-prime costs remain present. -/
namespace Erdos970.RecursiveSieve.Buchstab
open Finset Real Filter FiniteSelberg
set_option maxHeartbeats 1400000

theorem exists_uniform_variable_upper_tail :
    ∃ N : ℕ, ∀ M : ℝ, 13 ≤ M → ∀ n k : ℕ, N ≤ nthPrime k → ∀ s : ℝ, 1 ≤ s →
      eulerMass (nthPrime k).primesBelow*
        (∑ p ∈ terminalPart M k (s*log (nthPrime k : ℝ)), primeUpperExcess n (s*log (nthPrime k : ℝ)) p) ≤
        terminalAllowance initialTailCoefficient M/s := by
  obtain ⟨W,hW,h1,h2⟩ := exists_tail_threshold_wheel
  have hlog : Tendsto (fun n : ℕ => log (n : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨N,hN⟩ := eventually_atTop.mp ((eventually_ge_atTop (W*(firstHitWheel W)^2)).and
    ((hlog.eventually_ge_atTop 1).and eventually_eulerMass_initial_le_nine_fifths_log))
  refine ⟨N,fun M hM n k hk s hs => ?_⟩
  obtain ⟨hRW,hL,hEuler⟩ := hN (nthPrime k) hk
  apply le_trans _ (variable_initial_tail_finite k W hW h1 h2 hRW hL hEuler M s hM hs)
  apply mul_le_mul_of_nonneg_left _
    (eulerMass_pos _ (fun p hp => (Nat.mem_primesBelow.mp hp).2)).le
  apply sum_le_sum
  intro p hp
  have hpp := (Nat.mem_primesBelow.mp (mem_filter.mp hp).1).2
  exact (primeUpperExcess_le_zero n _ p).trans_eq (primeUpperExcess_zero _ p hpp)

theorem exists_uniform_variable_lower_tail :
    ∃ N : ℕ, ∀ M : ℝ, 13 ≤ M → ∀ n k : ℕ, N ≤ nthPrime k → ∀ s : ℝ, 1 ≤ s →
      eulerMass (nthPrime k).primesBelow*
        (∑ p ∈ terminalPart M k (s*log (nthPrime k : ℝ)), primeDeficit n (s*log (nthPrime k : ℝ)) p) ≤
        terminalAllowance lowerTailCoefficient M/s := by
  obtain ⟨N₀,hN₀⟩ := exists_lowerTailValid
  have hlog : Tendsto (fun n : ℕ => log (n : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨W,hW,hNW,hWlog⟩ := ((eventually_ge_atTop 1).and
    ((eventually_ge_atTop N₀).and (hlog.eventually_ge_atTop supportMassLogThreshold))).exists
  obtain ⟨N,hN⟩ := eventually_atTop.mp ((eventually_ge_atTop (W^3+W^2*(firstHitWheel W)^2)).and
    ((hlog.eventually_ge_atTop 1).and eventually_eulerMass_initial_le_nine_fifths_log))
  refine ⟨N,fun M hM n k hk s hs => ?_⟩
  obtain ⟨hRW,hL,hEuler⟩ := hN (nthPrime k) hk
  apply le_trans _ (variable_lower_tail_finite k W N₀ (by omega) hNW hN₀ hWlog hRW hL hEuler M s hM hs)
  apply mul_le_mul_of_nonneg_left _
    (eulerMass_pos _ (fun p hp => (Nat.mem_primesBelow.mp hp).2)).le
  exact sum_le_sum (fun p _ => primeDeficit_le_zero n _ p)

#print axioms exists_uniform_variable_upper_tail
#print axioms exists_uniform_variable_lower_tail
end Erdos970.RecursiveSieve.Buchstab
