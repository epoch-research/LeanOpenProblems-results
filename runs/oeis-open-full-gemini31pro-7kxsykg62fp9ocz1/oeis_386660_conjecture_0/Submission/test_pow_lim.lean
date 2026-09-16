import Mathlib
open Nat Filter Topology

lemma tendsto_root_n : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / (n : ℝ))) atTop (𝓝 1) := by
  have : Tendsto (fun x : ℝ => x ^ (1 / x)) atTop (𝓝 1) := tendsto_rpow_div
  exact this.comp tendsto_natCast_atTop_atTop

lemma a_sandwich (a M : ℕ → ℝ) (L : ℝ)
    (ha_pos : ∀ n, 0 < a n) (hM_pos : ∀ n, 0 < M n)
    (h_upper : ∀ n, 1 ≤ n → a n ≤ (n : ℝ) * M n)
    (h_lower : ∀ n, 1 ≤ n → M n ≤ (n : ℝ) * a n)
    (hL : Tendsto (fun n => M n ^ (1 / (n : ℝ))) atTop (𝓝 L)) :
    Tendsto (fun n => a n ^ (1 / (n : ℝ))) atTop (𝓝 L) := by
  have H_upper : ∀ᶠ n in atTop, a n ^ (1 / (n : ℝ)) ≤ (n : ℝ) ^ (1 / (n : ℝ)) * M n ^ (1 / (n : ℝ)) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have h1 : a n ≤ n * M n := h_upper n hn
    have h2 : a n ^ (1 / (n : ℝ)) ≤ ((n : ℝ) * M n) ^ (1 / (n : ℝ)) := Real.rpow_le_rpow (le_of_lt (ha_pos n)) h1 (by positivity)
    have h3 : ((n : ℝ) * M n) ^ (1 / (n : ℝ)) = (n : ℝ) ^ (1 / (n : ℝ)) * M n ^ (1 / (n : ℝ)) := by
      apply Real.mul_rpow (by positivity) (le_of_lt (hM_pos n))
    rwa [h3] at h2
  have H_lower : ∀ᶠ n in atTop, M n ^ (1 / (n : ℝ)) / (n : ℝ) ^ (1 / (n : ℝ)) ≤ a n ^ (1 / (n : ℝ)) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have h1 : M n ≤ n * a n := h_lower n hn
    have h2 : M n ^ (1 / (n : ℝ)) ≤ ((n : ℝ) * a n) ^ (1 / (n : ℝ)) := Real.rpow_le_rpow (le_of_lt (hM_pos n)) h1 (by positivity)
    have h3 : ((n : ℝ) * a n) ^ (1 / (n : ℝ)) = (n : ℝ) ^ (1 / (n : ℝ)) * a n ^ (1 / (n : ℝ)) := by
      apply Real.mul_rpow (by positivity) (le_of_lt (ha_pos n))
    rw [h3] at h2
    have hp : 0 < (n : ℝ) ^ (1 / (n : ℝ)) := by positivity
    rw [div_le_iff₀ hp, mul_comm]
    exact h2
  have h_lim_upper : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / (n : ℝ)) * M n ^ (1 / (n : ℝ))) atTop (𝓝 (1 * L)) :=
    Tendsto.mul tendsto_root_n hL
  rw [one_mul] at h_lim_upper
  have h_lim_lower : Tendsto (fun n : ℕ => M n ^ (1 / (n : ℝ)) / (n : ℝ) ^ (1 / (n : ℝ))) atTop (𝓝 (L / 1)) :=
    Tendsto.div hL tendsto_root_n one_ne_zero
  rw [div_one] at h_lim_lower
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' h_lim_lower h_lim_upper H_lower H_upper
