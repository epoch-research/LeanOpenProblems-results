import Mathlib
import Submission.Helper10
import Submission.Helper15

lemma W_bound_tendsto_N (C : ℕ) :
  Filter.Tendsto (fun N : ℕ => (((Nat.digits 10 N).length + 1 : ℝ)^C) / N) Filter.atTop (nhds 0) := by
  let k := fun N => (Nat.digits 10 N).length
  have hg : Filter.Tendsto (fun N : ℕ => (0 : ℝ)) Filter.atTop (nhds 0) := tendsto_const_nhds
  have hh1 : Filter.Tendsto (fun k : ℕ => ((k + 1 : ℝ)^C) / 10^k) Filter.atTop (nhds 0) := W_bound_tendsto C
  have hk : Filter.Tendsto k Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_atTop.mpr
    intro k_val
    use 10^k_val
    intros n hn
    have h1 : 1 < 10 := by decide
    have h2 := Nat.lt_base_pow_length_digits h1 (m := n)
    have h3 : 10^k_val < 10^(Nat.digits 10 n).length := by omega
    have h4 := (Nat.pow_lt_pow_iff_right (by decide)).mp h3
    exact h4.le
  have hh2 : Filter.Tendsto (fun N : ℕ => (((k N) + 1 : ℝ)^C) / 10^(k N)) Filter.atTop (nhds 0) := Filter.Tendsto.comp hh1 hk
  have hh : Filter.Tendsto (fun N : ℕ => 10 * ((((k N) + 1 : ℝ)^C) / 10^(k N))) Filter.atTop (nhds (10 * 0)) := Filter.Tendsto.const_mul 10 hh2
  simp at hh
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hg hh
  · intro N
    apply div_nonneg
    · positivity
    · positivity
  · intro N
    by_cases hN : N = 0
    · simp [hN]
      positivity
    · have h1 : 1 < 10 := by decide
      have h2 := Nat.base_pow_length_digits_le 10 N h1 hN
      have h3 : (10 ^ k N : ℝ) ≤ 10 * (N : ℝ) := by
        exact_mod_cast h2
      have h4 : 1 / (N : ℝ) ≤ 10 / (10 ^ k N : ℝ) := by
        rw [div_le_div_iff₀]
        · linarith
        · positivity
        · positivity
      calc (((k N) + 1 : ℝ) ^ C) / (N : ℝ)
        _ = (((k N) + 1 : ℝ) ^ C) * (1 / (N : ℝ)) := by ring
        _ ≤ (((k N) + 1 : ℝ) ^ C) * (10 / (10 ^ k N : ℝ)) := by
            apply mul_le_mul_of_nonneg_left h4
            positivity
        _ = 10 * ((((k N) + 1 : ℝ) ^ C) / (10 ^ k N : ℝ)) := by ring
