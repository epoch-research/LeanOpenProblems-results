import FormalConjectures.Util.ProblemImports

import Submission.Spec

open BigOperators Nat Int Real Asymptotics Filter

lemma descFactorial_ge_two (n k : ℕ) (hk : 2 ≤ k) (hn : k < n) :
    (n - 1) * (n - 2) ≤ Nat.descFactorial (n - 1) k := by
  have hn2 : 2 ≤ n - 1 := by omega
  have h_mul := Nat.descFactorial_mul_descFactorial (n := n - 1) (k := 2) (m := k) hk
  have h_two : Nat.descFactorial (n - 1) 2 = (n - 1) * (n - 2) := by
    have : n - 1 - 1 = n - 2 := by omega
    simp [Nat.descFactorial_succ, this]
    ring
  rw [← h_mul, h_two]
  have h_pos : 0 < Nat.descFactorial (n - 1 - 2) (k - 2) := by
    rw [Nat.descFactorial_pos]
    omega
  have h_ge_one : 1 ≤ Nat.descFactorial (n - 1 - 2) (k - 2) := h_pos
  have h_le := Nat.mul_le_mul_right ((n - 1) * (n - 2)) h_ge_one
  rw [Nat.one_mul] at h_le
  exact h_le

noncomputable def nat_fac_to_real (n : ℕ) : ℝ := (Nat.factorial n : ℝ)

noncomputable def menage_denom_term (n k : ℕ) : ℝ :=
  let k_fac_R := nat_fac_to_real k
  let falling_fac := (Nat.descFactorial (n - 1) k : ℝ)
  k_fac_R * falling_fac

lemma menage_denom_term_ge (n k : ℕ) (hk : 2 ≤ k) (hn : k < n) :
    2 * (((n - 1) * (n - 2) : ℕ) : ℝ) ≤ menage_denom_term n k := by
  have h1 : (2 : ℝ) ≤ (Nat.factorial k : ℝ) := by
    have : 2 ≤ Nat.factorial k := by
      have h_fac := Nat.factorial_le hk
      exact h_fac
    exact_mod_cast this
  have h2 : (((n - 1) * (n - 2) : ℕ) : ℝ) ≤ (Nat.descFactorial (n - 1) k : ℝ) := by
    have h_desc := descFactorial_ge_two n k hk hn
    exact_mod_cast h_desc
  unfold menage_denom_term nat_fac_to_real
  have h3 : (0 : ℝ) ≤ (((n - 1) * (n - 2) : ℕ) : ℝ) := by positivity
  have h4 : (0 : ℝ) ≤ (Nat.descFactorial (n - 1) k : ℝ) := by positivity
  nlinarith

lemma term_bound (n k : ℕ) (hk : 2 ≤ k) (hn : k < n) (hn3 : 3 ≤ n) :
    |((-1 : ℝ)^k) / menage_denom_term n k| ≤ 1 / (2 * (((n - 1) * (n - 2) : ℕ) : ℝ)) := by
  have h_denom : 2 * (((n - 1) * (n - 2) : ℕ) : ℝ) ≤ menage_denom_term n k := menage_denom_term_ge n k hk hn
  have h_pos_denom : 0 < 2 * (((n - 1) * (n - 2) : ℕ) : ℝ) := by
    have : 0 < (n - 1) * (n - 2) := by
      have : n - 1 ≥ 2 := by omega
      have : n - 2 ≥ 1 := by omega
      positivity
    positivity
  have h_abs_num : |(-1 : ℝ)^k| = 1 := by
    rw [abs_pow, abs_neg, abs_one, one_pow]
  have h_abs_denom : |menage_denom_term n k| = menage_denom_term n k := by
    have : 0 < menage_denom_term n k := by linarith
    exact abs_of_pos this
  rw [abs_div, h_abs_num, h_abs_denom]
  have h_le : 1 / menage_denom_term n k ≤ 1 / (2 * (((n - 1) * (n - 2) : ℕ) : ℝ)) := by
    rw [_root_.one_div_le_one_div] <;> linarith
  exact h_le

lemma sum_range_split (m : ℕ) (f : ℕ → ℝ) :
    ∑ i ∈ Finset.range (m + 2), f i = f 0 + f 1 + ∑ i ∈ Finset.range m, f (i + 2) := by
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  ring

noncomputable def A258667_asymptotic_sum_part (n : ℕ) : ℝ :=
  Finset.sum (Finset.range n) fun k =>
    if k = 0 then 0
    else
      let denom := menage_denom_term n k
      if denom = 0 then 0
      else ((-1 : ℝ) ^ k) / denom

lemma sum_part_eq (n : ℕ) (hn3 : 3 ≤ n) :
    A258667_asymptotic_sum_part n = -1 / (n - 1 : ℝ) + ∑ k ∈ Finset.range (n - 2), ((-1 : ℝ)^(k + 2)) / menage_denom_term n (k + 2) := by
  unfold A258667_asymptotic_sum_part
  have h_eq : n = (n - 2) + 2 := by omega
  have h_add : n - 2 + 2 = n := by omega
  conv_lhs => rw [h_eq]
  rw [sum_range_split (n - 2)]
  simp_rw [h_add]
  have h1 : (if 1 = 0 then (0 : ℝ) else if menage_denom_term n 1 = 0 then 0 else (-1) ^ 1 / menage_denom_term n 1) = -1 / (n - 1 : ℝ) := by
    have h1_ne : 1 ≠ 0 := by decide
    rw [if_neg h1_ne]
    have h_denom : menage_denom_term n 1 = (((n - 1 : ℕ) : ℝ)) := by
      unfold menage_denom_term nat_fac_to_real
      have h_desc : Nat.descFactorial (n - 1) 1 = n - 1 := Nat.descFactorial_one (n - 1)
      have h_fac : Nat.factorial 1 = 1 := rfl
      rw [h_desc, h_fac]
      simp
    have h_denom_ne : (menage_denom_term n 1 : ℝ) ≠ 0 := by
      rw [h_denom]
      have : n - 1 ≠ 0 := by omega
      exact_mod_cast this
    rw [if_neg h_denom_ne, h_denom]
    have h_sub : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      have h_sub_raw : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - ((1 : ℕ) : ℝ) := Nat.cast_sub (show 1 ≤ n by omega)
      rw [h_sub_raw]
      simp
    rw [h_sub]
    ring
  have h2 (k : ℕ) (hk : k < n - 2) :
      (if k + 2 = 0 then (0 : ℝ) else if menage_denom_term n (k + 2) = 0 then 0 else (-1) ^ (k + 2) / menage_denom_term n (k + 2)) =
      (-1) ^ (k + 2) / menage_denom_term n (k + 2) := by
    have h_ne : k + 2 ≠ 0 := by omega
    rw [if_neg h_ne]
    have h_denom_ne : menage_denom_term n (k + 2) ≠ 0 := by
      have hk2 : 2 ≤ k + 2 := by omega
      have hkn : k + 2 < n := by omega
      have h_ge := menage_denom_term_ge n (k + 2) hk2 hkn
      have h_pos : 0 < 2 * (((n - 1) * (n - 2) : ℕ) : ℝ) := by
        have : 0 < (n - 1) * (n - 2) := by
          have : n - 1 ≥ 2 := by omega
          have : n - 2 ≥ 1 := by omega
          positivity
        positivity
      linarith
    rw [if_neg h_denom_ne]
  rw [if_pos True.intro, h1, zero_add]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  exact h2 k hk

lemma asymptotic_sum_part_bound (n : ℕ) (hn3 : 3 ≤ n) :
    |A258667_asymptotic_sum_part n| ≤ 1 / (n - 1 : ℝ) + (n : ℝ) / (2 * (((n - 1) * (n - 2) : ℕ) : ℝ)) := by
  rw [sum_part_eq n hn3]
  have h_tri : |-1 / (n - 1 : ℝ) + ∑ k ∈ Finset.range (n - 2), ((-1 : ℝ)^(k + 2)) / menage_denom_term n (k + 2)| ≤
               |-1 / (n - 1 : ℝ)| + |∑ k ∈ Finset.range (n - 2), ((-1 : ℝ)^(k + 2)) / menage_denom_term n (k + 2)| := abs_add_le _ _
  have h_term1 : |-1 / (n - 1 : ℝ)| = 1 / (n - 1 : ℝ) := by
    have : (n : ℝ) - 1 > 0 := by
      have : (n : ℝ) ≥ 3 := by exact_mod_cast hn3
      linarith
    rw [abs_div, abs_neg, abs_one]
    rw [abs_of_pos this]
  have h_term2 : |∑ k ∈ Finset.range (n - 2), ((-1 : ℝ)^(k + 2)) / menage_denom_term n (k + 2)| ≤
                 (n : ℝ) / (2 * (((n - 1) * (n - 2) : ℕ) : ℝ)) := by
    have h_abs_sum := Finset.abs_sum_le_sum_abs (s := Finset.range (n - 2)) (f := fun k => ((-1 : ℝ)^(k + 2)) / menage_denom_term n (k + 2))
    have h_sum_le : ∑ k ∈ Finset.range (n - 2), |((-1 : ℝ)^(k + 2)) / menage_denom_term n (k + 2)| ≤
                    ∑ k ∈ Finset.range (n - 2), 1 / (2 * (((n - 1) * (n - 2) : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro k hk
      rw [Finset.mem_range] at hk
      have hk2 : 2 ≤ k + 2 := by omega
      have hkn : k + 2 < n := by omega
      exact term_bound n (k + 2) hk2 hkn hn3
    have h_sum_const : ∑ k ∈ Finset.range (n - 2), (1 / (2 * (((n - 1) * (n - 2) : ℕ) : ℝ))) =
                      ((n - 2 : ℕ) : ℝ) * (1 / (2 * (((n - 1) * (n - 2) : ℕ) : ℝ))) := by
      rw [Finset.sum_const]
      simp [nsmul_eq_mul]
    have h_le : ((n - 2 : ℕ) : ℝ) * (1 / (2 * (((n - 1) * (n - 2) : ℕ) : ℝ))) ≤
                (n : ℝ) / (2 * (((n - 1) * (n - 2) : ℕ) : ℝ)) := by
      have : ((n - 2 : ℕ) : ℝ) ≤ (n : ℝ) := by
        have : n - 2 ≤ n := by omega
        exact_mod_cast this
      have h_pos : 0 < 2 * (((n - 1) * (n - 2) : ℕ) : ℝ) := by
        have : 0 < (n - 1) * (n - 2) := by
          have : n - 1 ≥ 2 := by omega
          have : n - 2 ≥ 1 := by omega
          positivity
        positivity
      rw [mul_one_div]
      exact div_le_div_of_nonneg_right this h_pos.le
    linarith [h_abs_sum, h_sum_le, h_sum_const, h_le]
  linarith

lemma second_term_bound (n : ℕ) (hn4 : 4 ≤ n) :
    (n : ℝ) / (2 * (((n - 1) * (n - 2) : ℕ) : ℝ)) ≤ 1 / (n - 3 : ℝ) := by
  have h_sub1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    have h_sub_raw : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - ((1 : ℕ) : ℝ) := Nat.cast_sub (show 1 ≤ n by omega)
    rw [h_sub_raw]; simp
  have h_sub2 : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by
    have h_sub_raw : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - ((2 : ℕ) : ℝ) := Nat.cast_sub (show 2 ≤ n by omega)
    rw [h_sub_raw]; simp
  have h_denom : (2 * (((n - 1) * (n - 2) : ℕ) : ℝ)) = 2 * ((n : ℝ) - 1) * ((n : ℝ) - 2) := by
    push_cast
    rw [h_sub1, h_sub2]
    ring
  rw [h_denom]
  have h_pos1 : (n : ℝ) - 3 > 0 := by
    have : (n : ℝ) ≥ 4 := by exact_mod_cast hn4
    linarith
  have h_pos2 : 2 * ((n : ℝ) - 1) * ((n : ℝ) - 2) > 0 := by
    have : (n : ℝ) ≥ 4 := by exact_mod_cast hn4
    nlinarith
  have h_le : (n : ℝ) * ((n : ℝ) - 3) ≤ 2 * ((n : ℝ) - 1) * ((n : ℝ) - 2) := by
    have : (n : ℝ) ≥ 4 := by exact_mod_cast hn4
    nlinarith
  rw [div_le_iff₀ h_pos2, one_div_mul_eq_div, le_div_iff₀ h_pos1]
  exact h_le

lemma tendsto_two_div_n : Tendsto (fun n : ℕ => 2 / (n : ℝ)) atTop (nhds 0) := by
  have h_eq : (0 : ℝ) = 2 * 0 := by ring
  conv_rhs => rw [h_eq]
  have h_mul : Tendsto (fun n : ℕ => 2 * (1 / (n : ℝ))) atTop (nhds (2 * 0)) := by
    exact Tendsto.mul tendsto_const_nhds tendsto_one_div_atTop_nhds_zero_nat
  simp_rw [mul_one_div] at h_mul
  exact h_mul

lemma tendsto_one_div_sub_one : Tendsto (fun n : ℕ => 1 / (n - 1 : ℝ)) atTop (nhds 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun (_ : ℕ) => (0 : ℝ)) (h := fun (n : ℕ) => 2 / (n : ℝ)) ?_ tendsto_two_div_n ?_ ?_
  · exact tendsto_const_nhds
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have h_n : (n : ℝ) ≥ 2 := by exact_mod_cast hn
    have h_pos : (n : ℝ) - 1 > 0 := by linarith
    exact div_nonneg (by linarith) h_pos.le
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have h_n : (n : ℝ) ≥ 2 := by exact_mod_cast hn
    have h_pos : (n : ℝ) - 1 > 0 := by linarith
    have h_pos_n : (n : ℝ) > 0 := by linarith
    rw [div_le_div_iff₀ h_pos h_pos_n]
    linarith

lemma tendsto_one_div_sub_three : Tendsto (fun n : ℕ => 1 / (n - 3 : ℝ)) atTop (nhds 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun (_ : ℕ) => (0 : ℝ)) (h := fun (n : ℕ) => 2 / (n : ℝ)) ?_ tendsto_two_div_n ?_ ?_
  · exact tendsto_const_nhds
  · filter_upwards [eventually_ge_atTop 4] with n hn
    have h_n : (n : ℝ) ≥ 4 := by exact_mod_cast hn
    have h_pos : (n : ℝ) - 3 > 0 := by linarith
    exact div_nonneg (by linarith) h_pos.le
  · filter_upwards [eventually_ge_atTop 6] with n hn
    have h_n : (n : ℝ) ≥ 6 := by exact_mod_cast hn
    have h_pos : (n : ℝ) - 3 > 0 := by linarith
    have h_pos_n : (n : ℝ) > 0 := by linarith
    rw [div_le_div_iff₀ h_pos h_pos_n]
    linarith


lemma asymptotic_sum_part_bound_four (n : ℕ) (hn4 : 4 ≤ n) :
    |A258667_asymptotic_sum_part n| ≤ 1 / (n - 1 : ℝ) + 1 / (n - 3 : ℝ) := by
  have h1 := asymptotic_sum_part_bound n (by omega)
  have h2 := second_term_bound n hn4
  linarith

lemma tendsto_asymptotic_sum_part : Tendsto A258667_asymptotic_sum_part atTop (nhds 0) := by
  have h_bound : ∀ᶠ (n : ℕ) in atTop, |A258667_asymptotic_sum_part n| ≤ 1 / (n - 1 : ℝ) + 1 / (n - 3 : ℝ) := by
    filter_upwards [eventually_ge_atTop 4] with n hn
    exact asymptotic_sum_part_bound_four n hn
  have h_limit : Tendsto (fun n : ℕ => 1 / (n - 1 : ℝ) + 1 / (n - 3 : ℝ)) atTop (nhds 0) := by
    have : (0 : ℝ) = 0 + 0 := by ring
    conv_rhs => rw [this]
    exact Tendsto.add tendsto_one_div_sub_one tendsto_one_div_sub_three
  have h_limit_neg : Tendsto (fun n : ℕ => - (1 / (n - 1 : ℝ) + 1 / (n - 3 : ℝ))) atTop (nhds 0) := by
    have : (0 : ℝ) = -0 := by ring
    conv_rhs => rw [this]
    exact Tendsto.neg h_limit
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun (n : ℕ) => - (1 / (n - 1 : ℝ) + 1 / (n - 3 : ℝ))) (h := fun (n : ℕ) => 1 / (n - 1 : ℝ) + 1 / (n - 3 : ℝ)) h_limit_neg h_limit ?_ ?_
  · filter_upwards [h_bound] with n hn
    have : |A258667_asymptotic_sum_part n| ≤ 1 / (n - 1 : ℝ) + 1 / (n - 3 : ℝ) := hn
    rw [abs_le] at this
    exact this.1
  · filter_upwards [h_bound] with n hn
    have : |A258667_asymptotic_sum_part n| ≤ 1 / (n - 1 : ℝ) + 1 / (n - 3 : ℝ) := hn
    rw [abs_le] at this
    exact this.2


lemma eventually_one_add_sum_part_ne_zero : ∀ᶠ (n : ℕ) in atTop, 1 + A258667_asymptotic_sum_part n ≠ 0 := by
  have h_limit : Tendsto (fun n => 1 + A258667_asymptotic_sum_part n) atTop (nhds (1 + 0)) := by
    exact Tendsto.const_add 1 tendsto_asymptotic_sum_part
  have h_ne : (1 : ℝ) + 0 ≠ 0 := by linarith
  exact Tendsto.eventually_ne h_limit h_ne


lemma eventually_asymptotic_term_ne_zero : ∀ᶠ (x : ℕ) in atTop, A258667_asymptotic_term x ≠ 0 := by
  filter_upwards [eventually_ge_atTop 3, eventually_one_add_sum_part_ne_zero] with x hx1 hx2
  unfold A258667_asymptotic_term
  have : ¬ x ≤ 2 := by omega
  simp [this]
  have h_exp : exp (-2) ≠ 0 := by
    have : exp (-2) > 0 := exp_pos (-2)
    linarith
  have h_fac : nat_fac_to_real x ≠ 0 := by
    unfold nat_fac_to_real
    have : (x.factorial : ℝ) > 0 := by positivity
    linarith
  have h_div : (x : ℝ) - 2 ≠ 0 := by
    have : (x : ℝ) ≥ 3 := by exact_mod_cast hx1
    linarith
  have h_pref : exp (-2) * (nat_fac_to_real x / ((x : ℝ) - 2)) ≠ 0 := by
    apply mul_ne_zero h_exp
    exact div_ne_zero h_fac h_div
  exact mul_ne_zero h_pref hx2

theorem first_goal_proof : ∀ᶠ (x : ℕ) in atTop, A258667_asymptotic_term x = 0 → (A258667 x : ℝ) = 0 := by
  filter_upwards [eventually_asymptotic_term_ne_zero] with x hx
  intro h
  exact (hx h).elim












