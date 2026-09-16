import Mathlib

open Filter Topology

lemma length_digits_tendsto :
  Tendsto (fun N => (Nat.digits 10 N).length) atTop atTop := by
  apply tendsto_atTop_atTop.mpr
  intro k
  use 10^k
  intros n hn
  have h1 : 1 < 10 := by decide
  have h2 := Nat.lt_base_pow_length_digits h1 (m := n)
  have h3 : 10^k < 10^(Nat.digits 10 n).length := by omega
  have h4 := (Nat.pow_lt_pow_iff_right (by decide)).mp h3
  omega

lemma my_tendsto (C : ℕ) : Filter.Tendsto (fun k : ℕ => ((k + 1 : ℝ)^C) / 10^k) Filter.atTop (nhds 0) := by
  have h1 : 1 < (10 : ℝ) := by norm_num
  have h2 := tendsto_pow_const_div_const_pow_of_one_lt C h1
  have h3 : Tendsto (fun k : ℕ => k + 1) atTop atTop := tendsto_add_atTop_nat 1
  have h4 := Tendsto.comp h2 h3
  have h4' : Tendsto (fun k : ℕ => ((k + 1 : ℝ)^C) / 10^(k+1)) atTop (nhds 0) := by
    have eq : ((fun n : ℕ => (n : ℝ)^C / 10^n) ∘ fun k : ℕ => k + 1) = fun k : ℕ => ((k + 1 : ℝ)^C) / 10^(k+1) := by
      ext k
      simp
    rw [eq] at h4
    exact h4
  have h5 : Tendsto (fun k : ℕ => 10 * (((k + 1 : ℝ)^C) / 10^(k+1))) atTop (nhds (10 * 0)) := by
    apply Tendsto.const_mul 10
    exact h4'
  have h6 : (fun k : ℕ => 10 * (((k + 1 : ℝ)^C) / 10^(k+1))) = (fun k : ℕ => ((k + 1 : ℝ)^C) / 10^k) := by
    ext k
    simp [pow_succ']
    ring
  rw [←h6]
  simp at h5
  exact h5

lemma tendsto_bound_W (C : ℕ) :
  Tendsto (fun N : ℕ => (((Nat.digits 10 N).length + 1 : ℝ)^C) / N) atTop (nhds 0) := by
  let k := fun N => (Nat.digits 10 N).length
  have hg : Tendsto (fun N : ℕ => (0 : ℝ)) atTop (nhds 0) := tendsto_const_nhds
  have hh1 : Tendsto (fun k : ℕ => ((k + 1 : ℝ)^C) / 10^k) atTop (nhds 0) := my_tendsto C
  have hh2 : Tendsto (fun N : ℕ => (((k N) + 1 : ℝ)^C) / 10^(k N)) atTop (nhds 0) := Tendsto.comp hh1 length_digits_tendsto
  have hh : Tendsto (fun N : ℕ => 10 * ((((k N) + 1 : ℝ)^C) / 10^(k N))) atTop (nhds (10 * 0)) := Tendsto.const_mul 10 hh2
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
