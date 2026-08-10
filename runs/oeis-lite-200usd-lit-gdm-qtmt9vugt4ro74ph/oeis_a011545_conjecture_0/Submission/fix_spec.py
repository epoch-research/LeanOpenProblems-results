# Read Spec.lean.bak
with open("/workspace/leanproject/Submission/Spec.lean.bak", "r") as f:
    lines = f.readlines()

# Find the start and end of subgoal_T_60
start_idx = -1
end_idx = -1
for i, line in enumerate(lines):
    if "lemma subgoal_T_60 : T_prop 60" in line:
        start_idx = i
    if start_idx != -1 and "lemma subgoal_S_60" in line:
        end_idx = i
        break

print(f"subgoal_T_60 found from line {start_idx} to {end_idx}")

new_proof = """lemma subgoal_T_60 : T_prop 60 := by
  intro Y r hr1 hr2
  intro ⟨q, h1, h2⟩
  have h_pi_gt : 3.141592653589793238462643383279502884197169399375105820974944592307816406286208 < Real.pi := pi_gt_60
  have h_pi_lt : Real.pi < 3.141592653589793238462643383279502884197169399375105820974944592307816406286210 := pi_lt_60
  have h_pow_cast_real : (10 : ℝ) ^ (60 + Y) = (10 : ℝ) ^ 60 * (10 : ℝ) ^ Y := by rw [pow_add]
  have h_pow_cast_real_60 : (10 : ℝ) ^ 60 = 1000000000000000000000000000000000000000000000000000000000000 := by norm_num
  have h_ten_neg : 2 * (10 : ℝ) ^ (-( ((60 : ℕ) : ℤ) + (Y : ℤ) + 2 )) ≤ 2 * (10 : ℝ) ^ (-62 : ℤ) := by
    have : -( (60 : ℤ) + (Y : ℤ) + 2 ) ≤ -62 := by omega
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 10) this
  have h_ten_neg_val : 2 * (10 : ℝ) ^ (-62 : ℤ) = 2 / 100000000000000000000000000000000000000000000000000000000000000 := by norm_num
  have h_lt_62 : (q : ℝ) < Real.pi * (10 : ℝ) ^ 60 * (10 : ℝ) ^ Y - (r : ℝ) / 10 + 2 * (10 : ℝ) ^ (-62 : ℤ) := by
    have h2_rw := h2
    rw [h_pow_cast_real] at h2_rw
    have h_eq_cast : (-(60 + Y + 2 : ℤ)) = -(60 + Y + 2 : ℤ) := rfl
    push_cast at h2_rw
    linarith [h2_rw, h_ten_neg]
  have h_gt_62 : Real.pi * (10 : ℝ) ^ 60 * (10 : ℝ) ^ Y - (r : ℝ) / 10 < (q : ℝ) := by
    have h1_rw := h1
    rw [h_pow_cast_real] at h1_rw
    push_cast at h1_rw
    linarith
  have hY_ge : (10 : ℝ) ^ Y ≥ 1 := one_le_pow₀ (by norm_num)
  have h_pi_scaled_gt : 3141592653589793238462643383279502884197169399375105820974944.592307816406286208 * (10 : ℝ) ^ Y < Real.pi * (10 : ℝ) ^ 60 * (10 : ℝ) ^ Y := by
    have h_scale : (3141592653589793238462643383279502884197169399375105820974944.592307816406286208 : ℝ) = 3.141592653589793238462643383279502884197169399375105820974944592307816406286208 * (10 : ℝ) ^ 60 := by norm_num
    rw [h_scale]
    rw [mul_assoc, mul_assoc]
    exact mul_lt_mul_of_pos_right h_pi_gt (by positivity)
  have h_pi_scaled_lt : Real.pi * (10 : ℝ) ^ 60 * (10 : ℝ) ^ Y < 3141592653589793238462643383279502884197169399375105820974944.592307816406286210 * (10 : ℝ) ^ Y := by
    have h_scale : (3141592653589793238462643383279502884197169399375105820974944.592307816406286210 : ℝ) = 3.141592653589793238462643383279502884197169399375105820974944592307816406286210 * (10 : ℝ) ^ 60 := by norm_num
    rw [h_scale]
    rw [mul_assoc, mul_assoc]
    exact mul_lt_mul_of_pos_right h_pi_lt (by positivity)
  have h_or : r ≤ 5 ∨ 6 ≤ r := by omega
  rcases h_or with hr_le5 | hr_ge6
  · have hr_le5_real : (r : ℝ) ≤ 5 := by exact_mod_cast hr_le5
    have hr1_real : (1 : ℝ) ≤ r := by exact_mod_cast hr1
    have h_q_gt : ((3141592653589793238462643383279502884197169399375105820974944 : ℝ) * (10 : ℝ) ^ Y < (q : ℝ)) := by
      calc ((3141592653589793238462643383279502884197169399375105820974944 : ℝ) * (10 : ℝ) ^ Y)
        _ < (Real.pi * (10 : ℝ) ^ 60 - (r : ℝ) / 10) * (10 : ℝ) ^ Y := by
          have : (3141592653589793238462643383279502884197169399375105820974944 : ℝ) < Real.pi * (10 : ℝ) ^ 60 - (r : ℝ) / 10 := by
            calc (3141592653589793238462643383279502884197169399375105820974944 : ℝ)
              _ < 3141592653589793238462643383279502884197169399375105820974944.592307816406286208 - 5 / 10 := by norm_num
              _ ≤ 3141592653589793238462643383279502884197169399375105820974944.592307816406286208 - (r : ℝ) / 10 := by linarith
              _ < Real.pi * (10 : ℝ) ^ 60 - (r : ℝ) / 10 := by linarith [h_pi_gt]
          exact mul_lt_mul_of_pos_right this (by positivity)
        _ = Real.pi * (10 : ℝ) ^ 60 * (10 : ℝ) ^ Y - (r : ℝ) / 10 * (10 : ℝ) ^ Y := by ring
        _ ≤ Real.pi * (10 : ℝ) ^ 60 * (10 : ℝ) ^ Y - (r : ℝ) / 10 := by
          have h_scale : (r : ℝ) / 10 ≤ (r : ℝ) / 10 * (10 : ℝ) ^ Y := by
            have : 0 ≤ (r : ℝ) / 10 := by linarith
            exact le_mul_of_one_le_right this hY_ge
          linarith
        _ < (q : ℝ) := h_gt_62
    have h_q_lt : ((q : ℝ) < (3141592653589793238462643383279502884197169399375105820974945 : ℝ) * (10 : ℝ) ^ Y) := by
      calc (q : ℝ)
        _ < Real.pi * (10 : ℝ) ^ 60 * (10 : ℝ) ^ Y - (r : ℝ) / 10 + 2 * (10 : ℝ) ^ (-62 : ℤ) := h_lt_62
        _ < Real.pi * (10 : ℝ) ^ 60 * (10 : ℝ) ^ Y + 2 * (10 : ℝ) ^ (-62 : ℤ) := by linarith
        _ ≤ (Real.pi * (10 : ℝ) ^ 60 + 2 * (10 : ℝ) ^ (-62 : ℤ)) * (10 : ℝ) ^ Y := by
          have h_scale_ten : 2 * (10 : ℝ) ^ (-62 : ℤ) ≤ 2 * (10 : ℝ) ^ (-62 : ℤ) * (10 : ℝ) ^ Y := by
            have h_nonneg : 0 ≤ 2 * (10 : ℝ) ^ (-62 : ℤ) := by
              apply mul_nonneg (by norm_num)
              exact zpow_nonneg (by norm_num : (0 : ℝ) ≤ 10) (-62 : ℤ)
            nth_rw 1 [← mul_one (2 * (10 : ℝ) ^ (-62 : ℤ))]
            exact mul_le_mul_of_nonneg_left hY_ge h_nonneg
          have : (Real.pi * (10 : ℝ) ^ 60 + 2 * (10 : ℝ) ^ (-62 : ℤ)) * (10 : ℝ) ^ Y = Real.pi * (10 : ℝ) ^ 60 * (10 : ℝ) ^ Y + 2 * (10 : ℝ) ^ (-62 : ℤ) * (10 : ℝ) ^ Y := by ring
          linarith
        _ < (3141592653589793238462643383279502884197169399375105820974945 : ℝ) * (10 : ℝ) ^ Y := by
          have h_scale : Real.pi * (10 : ℝ) ^ 60 + 2 * (10 : ℝ) ^ (-62 : ℤ) < (3141592653589793238462643383279502884197169399375105820974945 : ℝ) := by
            calc Real.pi * (10 : ℝ) ^ 60 + 2 * (10 : ℝ) ^ (-62 : ℤ)
              _ < 3141592653589793238462643383279502884197169399375105820974944.59230781640628621 + 2 * (10 : ℝ) ^ (-62 : ℤ) := by linarith [h_pi_lt]
              _ = 3141592653589793238462643383279502884197169399375105820974944.59230781640628621 + 2 / 100000000000000000000000000000000000000000000000000000000000000 := by rw [h_ten_neg_val]
              _ < (3141592653589793238462643383279502884197169399375105820974945 : ℝ) := by norm_num
          exact mul_lt_mul_of_pos_right h_scale (by positivity)
    have hk_gt : 3141592653589793238462643383279502884197169399375105820974944 * (10 : ℤ) ^ Y < q := by
      exact_mod_cast h_q_gt
    have hk_lt : q < 3141592653589793238462643383279502884197169399375105820974945 * (10 : ℤ) ^ Y := by
      exact_mod_cast h_q_lt
    have h_Z : (10 : ℤ) ^ Y ≥ 1 := one_le_pow₀ (by norm_num)
    omega
  · have hr_ge6_real : (6 : ℝ) ≤ r := by exact_mod_cast hr_ge6
    have hr2_real : (r : ℝ) ≤ 9 := by exact_mod_cast hr2
    have h_q_gt : ((3141592653589793238462643383279502884197169399375105820974943 : ℝ) * (10 : ℝ) ^ Y < (q : ℝ)) := by
      calc ((3141592653589793238462643383279502884197169399375105820974943 : ℝ) * (10 : ℝ) ^ Y)
        _ < (Real.pi * (10 : ℝ) ^ 60 - (r : ℝ) / 10) * (10 : ℝ) ^ Y := by
          have : (3141592653589793238462643383279502884197169399375105820974943 : ℝ) < Real.pi * (10 : ℝ) ^ 60 - (r : ℝ) / 10 := by
            calc (3141592653589793238462643383279502884197169399375105820974943 : ℝ)
              _ < 3141592653589793238462643383279502884197169399375105820974944.592307816406286208 - 9 / 10 := by norm_num
              _ ≤ 3141592653589793238462643383279502884197169399375105820974944.592307816406286208 - (r : ℝ) / 10 := by linarith
              _ < Real.pi * (10 : ℝ) ^ 60 - (r : ℝ) / 10 := by linarith [h_pi_gt]
          exact mul_lt_mul_of_pos_right this (by positivity)
        _ = Real.pi * (10 : ℝ) ^ 60 * (10 : ℝ) ^ Y - (r : ℝ) / 10 * (10 : ℝ) ^ Y := by ring
        _ ≤ Real.pi * (10 : ℝ) ^ 60 * (10 : ℝ) ^ Y - (r : ℝ) / 10 := by
          have h_scale : (r : ℝ) / 10 ≤ (r : ℝ) / 10 * (10 : ℝ) ^ Y := by
            have : 0 ≤ (r : ℝ) / 10 := by linarith
            exact le_mul_of_one_le_right this hY_ge
          linarith
        _ < (q : ℝ) := h_gt_62
    have h_q_lt : ((q : ℝ) < (3141592653589793238462643383279502884197169399375105820974944 : ℝ) * (10 : ℝ) ^ Y) := by
      calc (q : ℝ)
        _ < Real.pi * (10 : ℝ) ^ 60 * (10 : ℝ) ^ Y - (r : ℝ) / 10 + 2 * (10 : ℝ) ^ (-62 : ℤ) := h_lt_62
        _ < Real.pi * (10 : ℝ) ^ 60 * (10 : ℝ) ^ Y + 2 * (10 : ℝ) ^ (-62 : ℤ) := by linarith
        _ ≤ (Real.pi * (10 : ℝ) ^ 60 + 2 * (10 : ℝ) ^ (-62 : ℤ)) * (10 : ℝ) ^ Y := by
          have h_scale_ten : 2 * (10 : ℝ) ^ (-62 : ℤ) ≤ 2 * (10 : ℝ) ^ (-62 : ℤ) * (10 : ℝ) ^ Y := by
            have h_nonneg : 0 ≤ 2 * (10 : ℝ) ^ (-62 : ℤ) := by
              apply mul_nonneg (by norm_num)
              exact zpow_nonneg (by norm_num : (0 : ℝ) ≤ 10) (-62 : ℤ)
            nth_rw 1 [← mul_one (2 * (10 : ℝ) ^ (-62 : ℤ))]
            exact mul_le_mul_of_nonneg_left hY_ge h_nonneg
          have : (Real.pi * (10 : ℝ) ^ 60 + 2 * (10 : ℝ) ^ (-62 : ℤ)) * (10 : ℝ) ^ Y = Real.pi * (10 : ℝ) ^ 60 * (10 : ℝ) ^ Y + 2 * (10 : ℝ) ^ (-62 : ℤ) * (10 : ℝ) ^ Y := by ring
          linarith
        _ < (3141592653589793238462643383279502884197169399375105820974944 : ℝ) * (10 : ℝ) ^ Y := by
          have h_scale : Real.pi * (10 : ℝ) ^ 60 + 2 * (10 : ℝ) ^ (-62 : ℤ) < (3141592653589793238462643383279502884197169399375105820974944 : ℝ) := by
            calc Real.pi * (10 : ℝ) ^ 60 + 2 * (10 : ℝ) ^ (-62 : ℤ)
              _ < 3141592653589793238462643383279502884197169399375105820974944.59230781640628621 + 2 * (10 : ℝ) ^ (-62 : ℤ) := by linarith [h_pi_lt]
              _ = 3141592653589793238462643383279502884197169399375105820974944.59230781640628621 + 2 / 100000000000000000000000000000000000000000000000000000000000000 := by rw [h_ten_neg_val]
              _ < (3141592653589793238462643383279502884197169399375105820974944 : ℝ) := by norm_num
          exact mul_lt_mul_of_pos_right h_scale (by positivity)
    have hk_gt : 3141592653589793238462643383279502884197169399375105820974943 * (10 : ℤ) ^ Y < q := by
      exact_mod_cast h_q_gt
    have hk_lt : q < 3141592653589793238462643383279502884197169399375105820974944 * (10 : ℤ) ^ Y := by
      exact_mod_cast h_q_lt
    have h_Z : (10 : ℤ) ^ Y ≥ 1 := one_le_pow₀ (by norm_num)
    omega
"""

output_lines = lines[:start_idx] + [new_proof + "\\n"] + lines[end_idx:]

with open("/workspace/leanproject/Submission/Spec.lean", "w") as f:
    f.writelines(output_lines)

print("Spec.lean successfully generated!")
