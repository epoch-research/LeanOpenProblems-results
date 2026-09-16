import Mathlib

import Submission.Helper10
import Submission.Helper18
import Submission.Helper27
import Submission.Helper28

open Filter Topology Real

lemma tendsto_div_100 : Tendsto (fun N : ℕ => ((N / 100 : ℕ) : ℝ) / N) atTop (nhds (1 / 100)) := by
  have h_lower : ∀ N : ℕ, N > 0 → (1 / 100 : ℝ) - 1 / N ≤ ((N / 100 : ℕ) : ℝ) / N := by
    intro N hN
    have : ((N / 100 : ℕ) : ℝ) ≥ (N : ℝ) / 100 - 1 := by
      have h1 : (N / 100) * 100 + N % 100 = N := by omega
      have h2 : N % 100 < 100 := Nat.mod_lt N (by decide)
      have h3 : (N : ℝ) = (((N / 100 : ℕ) : ℝ) * 100 + ((N % 100 : ℕ) : ℝ)) := by exact_mod_cast h1.symm
      have h4 : ((N % 100 : ℕ) : ℝ) < 100 := by exact_mod_cast h2
      linarith
    have hN_pos : (N : ℝ) > 0 := Nat.cast_pos.mpr hN
    have H : ((N : ℝ) / 100 - 1) / N = (1 / 100 : ℝ) - 1 / N := by
      calc ((N : ℝ) / 100 - 1) / N
        _ = ((N : ℝ) / 100) / N - 1 / N := by rw [sub_div]
        _ = (N : ℝ) / (100 * N) - 1 / N := by rw [div_div]
        _ = (N : ℝ) / (N * 100) - 1 / N := by rw [mul_comm 100 _]
        _ = ((N : ℝ) / N) / 100 - 1 / N := by rw [← div_div]
        _ = 1 / 100 - 1 / N := by rw [div_self (ne_of_gt hN_pos)]
    rw [← H]
    exact div_le_div_of_nonneg_right this (le_of_lt hN_pos)
  have h_upper : ∀ N : ℕ, ((N / 100 : ℕ) : ℝ) / N ≤ 1 / 100 := by
    intro N
    by_cases hN : N = 0
    · simp [hN]
    · have hN_pos : (N : ℝ) > 0 := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
      have : ((N / 100 : ℕ) : ℝ) ≤ (N : ℝ) / 100 := by
        have h1 : (N / 100) * 100 + N % 100 = N := by omega
        have h3 : (N : ℝ) = (((N / 100 : ℕ) : ℝ) * 100 + ((N % 100 : ℕ) : ℝ)) := by exact_mod_cast h1.symm
        have h4 : 0 ≤ ((N % 100 : ℕ) : ℝ) := Nat.cast_nonneg _
        linarith
      calc ((N / 100 : ℕ) : ℝ) / N
        _ ≤ ((N : ℝ) / 100) / N := div_le_div_of_nonneg_right this (le_of_lt hN_pos)
        _ = 1 / 100 := by
            rw [div_div, mul_comm, ← div_div, div_self (ne_of_gt hN_pos)]
  let f := fun N : ℕ => if N > 0 then (1 / 100 : ℝ) - 1 / N else 0
  have h1 : Tendsto (fun N : ℕ => (1 / 100 : ℝ) - 1 / N) atTop (nhds (1 / 100 - 0)) := by
    apply Tendsto.sub
    · exact tendsto_const_nhds
    · exact tendsto_one_div_atTop_nhds_zero_nat
  rw [sub_zero] at h1
  have h_tendsto_f : Tendsto f atTop (nhds (1 / 100)) := by
    have eq : (fun N : ℕ => (1 / 100 : ℝ) - 1 / N) =ᶠ[atTop] f := by
      have : ∀ᶠ N in atTop, N > 0 := by
        apply eventually_atTop.mpr
        use 1
        intros b hb
        exact lt_of_lt_of_le (by decide) hb
      apply Eventually.mono this
      intro N hN
      dsimp [f]
      rw [if_pos hN]
    exact Tendsto.congr' eq h1
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le h_tendsto_f tendsto_const_nhds
  · intro N
    dsimp [f]
    by_cases h : N > 0
    · rw [if_pos h]
      exact h_lower N h
    · rw [if_neg h]
      have : N = 0 := by omega
      simp [this]
  · exact h_upper
