import re

with open('/workspace/leanproject/Submission/Spec.lean', 'r') as f:
    spec = f.read()

# We extract definitions from Spec.lean to keep them.
spec_head = spec[:spec.find('theorem oeis_206911_conjecture')]

with open('/workspace/leanproject/Submission/Complete.lean', 'r') as f:
    comp = f.read()

# Remove imports and definitions that are already in Spec.lean
comp_body = comp[comp.find('lemma harm_nonneg'):]

with open('/workspace/leanproject/Submission/LostLemmas.lean', 'r') as f:
    lost = f.read()
c_mono_le = lost[lost.find('lemma c_mono_le'):]

with open('/workspace/leanproject/Submission/A206911_eq.lean', 'r') as f:
    aeq = f.read()
aeq_body = aeq[aeq.find('lemma count_2s_add_count_3s_eq_N'):]

with open('/workspace/leanproject/Submission/TestLimitNormNum.lean', 'r') as f:
    lnn = f.read()
limit_bounds = lnn[lnn.find('lemma limit_bounds'):]

c1_bound = """
lemma c1_gt_1 : 1 < exp (harmonic 1) * (exp (1 / 2 : ℝ) - 1) := by
  have H : (5:ℝ)/2 ≤ exp 1 := by
    have : (1:ℝ) = 1 := rfl
    have H2 := exp_lower_bound_7 1 (by positivity)
    linarith
  have H2 : 1 + 1/2 + 1/8 ≤ exp (1/2 : ℝ) := by
    have H3 := exp_lower_bound_7 (1/2) (by positivity)
    linarith
  have hh : (harmonic 1 : ℝ) = 1 := by norm_num
  rw [hh]
  calc
    1 = (5/2 : ℝ) * (13/8 - 1) - 9/16 := by norm_num
    _ < (5/2 : ℝ) * (13/8 - 1) := by linarith
    _ ≤ exp 1 * (1 + 1/2 + 1/8 - 1) := by
      apply mul_le_mul H (by linarith) (by norm_num) (exp_pos _).le
    _ ≤ exp 1 * (exp (1/2 : ℝ) - 1) := by
      apply mul_le_mul_of_nonneg_left (by linarith) (exp_pos _).le
"""

final_thm = """
theorem oeis_206911_conjecture :
  (∀ n : ℕ, 1 ≤ n → A206911_diff n = 2 ∨ A206911_diff n = 3) ∧
  (∃ L : ℝ,
     (35/10 : ℝ) < L ∧ L < (36/10 : ℝ) ∧
     Tendsto (fun N : ℕ => (A206911_count_3s N : ℝ) / (A206911_count_2s N : ℝ)) atTop (nhds L))
:= by
  have h23 : ∀ n : ℕ, 1 ≤ n → A206911_diff n = 2 ∨ A206911_diff n = 3 := by
    intro n hn
    apply diff_eq_2_or_3
    · apply harm_nonneg
    · apply harm_nonneg
    · constructor
      · have h_cn := c_mono_le (fun k hk => (c_mono k hk).le) 1 n (by omega) hn
        have hc_base : 1 < exp (harmonic 1) * (exp (1 / (1 + 1 : ℝ)) - 1) := by
          have h2 : (1 + 1 : ℝ) = 2 := by norm_num
          rw [h2]
          exact c1_gt_1
        have h_harm : exp (harmonic n) * (exp (1 / (n + 1 : ℝ)) - 1) = exp (harmonic (n + 1)) - exp (harmonic n) := by
          have : harmonic (n + 1) = harmonic n + (n + 1 : ℝ)⁻¹ := by rw [harmonic_succ]; exact_mod_cast rfl
          rw [this, one_div]
          rw [exp_add]
          ring
        rw [← h_harm]
        exact hc_base.trans_le h_cn
      · exact c_upper_bound n
  constructor
  · exact h23
  · use (exp eulerMascheroniConstant - 1) / (2 - exp eulerMascheroniConstant)
    constructor
    · have hL := limit_bounds (exp eulerMascheroniConstant) exp_gamma_lower exp_gamma_upper
      exact hL.1
    · constructor
      · have hL := limit_bounds (exp eulerMascheroniConstant) exp_gamma_lower exp_gamma_upper
        exact hL.2
      · have h_not_two : exp eulerMascheroniConstant ≠ 2 := by
          have h_up := exp_gamma_upper
          linarith
        exact tendsto_ratio A206911_mono h23 h_not_two

theorem oeis_206911_conjecture.disproof : ¬ (type_of% @oeis_206911_conjecture) := sorry
"""

out = spec_head + comp_body + "\n" + c_mono_le + "\n" + aeq_body + "\n" + limit_bounds + "\n" + c1_bound + "\n" + final_thm
with open('/workspace/leanproject/Submission/Spec2.lean', 'w') as f:
    f.write(out)
