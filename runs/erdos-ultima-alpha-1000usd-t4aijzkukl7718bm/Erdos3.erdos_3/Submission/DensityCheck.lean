import FormalConjecturesUtil

/-! A check of the proposed reduction to positive natural density.
This file does not prove or disprove the original conjecture. -/

open Filter
open scoped Topology

namespace Erdos3DensityCheck

theorem primeCounting'_div_self_tendsto_zero :
    Tendsto (fun n : ℕ ↦ (Nat.primeCounting' n : ℝ) / n) atTop (𝓝 0) := by
  have hbound : ∀ᶠ n : ℕ in atTop,
      (Nat.primeCounting n : ℝ) ≤ (Real.log 4 + 1) * n / Real.log n := by
    simpa using (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
      (Chebyshev.eventually_primeCounting_le (ε := 1) zero_lt_one)
  have hlim : Tendsto (fun n : ℕ ↦ (Real.log 4 + 1) / Real.log n) atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  apply squeeze_zero' (Eventually.of_forall (fun n ↦ by positivity)) ?_ hlim
  filter_upwards [hbound, eventually_ge_atTop 1] with n hn hn1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  calc
    (Nat.primeCounting' n : ℝ) / n ≤ (Nat.primeCounting n : ℝ) / n := by
      apply div_le_div_of_nonneg_right _ hnpos.le
      exact_mod_cast Nat.monotone_primeCounting' (Nat.le_succ n)
    _ ≤ ((Real.log 4 + 1) * n / Real.log n) / n :=
      div_le_div_of_nonneg_right hn hnpos.le
    _ = (Real.log 4 + 1) / Real.log n := by
      rw [div_right_comm, mul_div_cancel_right₀ _ (ne_of_gt hnpos)]

theorem primes_hasDensity_zero : {p : ℕ | p.Prime}.HasDensity 0 := by
  have heq (n : ℕ) : {p : ℕ | p.Prime} ∩ Set.Iio n = (n.primesBelow : Set ℕ) := by
    ext p
    simp [Nat.primesBelow, and_comm]
  simpa [Set.HasDensity, Set.partialDensity, heq,
    Nat.primesBelow_card_eq_primeCounting'] using primeCounting'_div_self_tendsto_zero

theorem divergence_does_not_imply_positive_density :
    ¬ (∀ A : Set ℕ, (¬ Summable fun a : A ↦ 1 / (a : ℝ)) → A.HasPosDensity) := by
  intro h
  have hprime : ¬ Summable fun a : {p : ℕ | p.Prime} ↦ 1 / (a : ℝ) :=
    Nat.Primes.not_summable_one_div
  obtain ⟨d, hd, hden⟩ := h {p : ℕ | p.Prime} hprime
  have heq : d = 0 := tendsto_nhds_unique hden primes_hasDensity_zero
  linarith

#print axioms divergence_does_not_imply_positive_density

end Erdos3DensityCheck
