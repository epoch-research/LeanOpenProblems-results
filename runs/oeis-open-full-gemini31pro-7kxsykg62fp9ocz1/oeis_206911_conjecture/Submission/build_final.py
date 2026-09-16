with open('/workspace/leanproject/Submission/Spec.lean', 'r') as f:
    spec = f.read()

# We need to remove c_mono_le and c_upper_bound from adiff_body injection if it is already there.
# Let's just build it all cleanly again.

with open('/workspace/leanproject/Submission/Spec.lean', 'r') as f:
    spec = f.read()
spec_head = spec[:spec.find('theorem oeis_206911_conjecture')]

with open('/workspace/leanproject/Submission/Complete.lean', 'r') as f:
    comp = f.read()
comp_body = comp[comp.find('lemma harm_nonneg'):]

with open('/workspace/leanproject/Submission/A206911_eq.lean', 'r') as f:
    aeq = f.read()
aeq_body = aeq[aeq.find('lemma count_2s_add_count_3s_eq_N'):]

aeq_body = aeq_body.replace('sum_diff_eq N h_mono', 'sum_diff_eq N')

with open('/workspace/leanproject/Submission/TestLimitNormNum.lean', 'r') as f:
    lnn = f.read()
limit_bounds = lnn[lnn.find('lemma limit_bounds'):]

with open('/workspace/leanproject/Submission/A206911_diff_eq.lean', 'r') as f:
    adiff = f.read()
adiff_body = adiff[adiff.find('lemma c1_gt_1'):]

final_thm = """
theorem oeis_206911_conjecture :
  (∀ n : ℕ, 1 ≤ n → A206911_diff n = 2 ∨ A206911_diff n = 3) ∧
  (∃ L : ℝ,
     (35/10 : ℝ) < L ∧ L < (36/10 : ℝ) ∧
     Tendsto (fun N : ℕ => (A206911_count_3s N : ℝ) / (A206911_count_2s N : ℝ)) atTop (nhds L))
:= by
  have h23 : ∀ n : ℕ, 1 ≤ n → A206911_diff n = 2 ∨ A206911_diff n = 3 := A206911_diff_eq_2_or_3
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

out = "\n".join([spec_head[:spec_head.rfind('\n/--\nConjecture: the')], comp_body, adiff_body, limit_bounds, aeq_body, final_thm])

with open('/workspace/leanproject/Submission/Spec.lean', 'w') as f:
    f.write(out)
