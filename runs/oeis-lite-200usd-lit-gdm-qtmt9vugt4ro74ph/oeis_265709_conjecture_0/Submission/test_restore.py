import os

path = "/workspace/leanproject/Submission/Spec.lean"
with open(path, 'r') as f:
    content = f.read()

old_case1 = """        have h_lt_sig2_cast : (2 : ℚ)^(padicValNat 2 (p + 1)) < (q1.den : ℚ) := by
          exact_mod_cast h_lt_sig2
        have h_contra1 : (p + 2 : ℚ) * (2 : ℚ)^(padicValNat 2 (p + 1)) ≤ (q1.den : ℚ) * (p + 1 : ℚ) := by
          calc (p + 2 : ℚ) * (2 : ℚ)^(padicValNat 2 (p + 1)) ≤ (p + 2 : ℚ) * (q2.den : ℚ) := mul_le_mul_of_nonneg_left h_pow_le (by positivity)
          _ ≤ (q1.den : ℚ) * (p + 1 : ℚ) := h_mul_le
        have h_contra2 : (q1.den : ℚ) * (p + 1 : ℚ) < (p + 2 : ℚ) * (2 : ℚ)^(padicValNat 2 (p + 1)) := by
          calc (q1.den : ℚ) * (p + 1 : ℚ) < (2 : ℚ)^(padicValNat 2 (p + 1)) * (p + 1 : ℚ) := mul_lt_mul_of_pos_right h_lt_sig2_cast hp_plus_one_pos
          _ < (2 : ℚ)^(padicValNat 2 (p + 1)) * (p + 2 : ℚ) := mul_lt_mul_of_pos_left (by linarith) (by positivity)
          _ = (p + 2 : ℚ) * (2 : ℚ)^(padicValNat 2 (p + 1)) := by ring
        linarith"""

new_case1 = """        have h_lt_sig2_cast : (2 : ℚ)^(padicValNat 2 (p + 1)) < (q1.den : ℚ) := by
          exact_mod_cast h_lt_sig2
        have h_contra1 : (2 : ℚ)^(padicValNat 2 (p + 1)) * (p + 1 : ℚ) < (q1.den : ℚ) * (p + 1 : ℚ) := by
          calc (2 : ℚ)^(padicValNat 2 (p + 1)) * (p + 1 : ℚ) < (q1.den : ℚ) * (p + 1 : ℚ) := mul_lt_mul_of_pos_right h_lt_sig2_cast hp_plus_one_pos
        sorry"""

if new_case1 in content:
    content = content.replace(new_case1, old_case1)
    print("Restored Case 1!")
else:
    print("Could not find the modified Case 1!")

with open(path, 'w') as f:
    f.write(content)
