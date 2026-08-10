import os

path = "/workspace/leanproject/Submission/Spec.lean"
with open(path, 'r') as f:
    content = f.read()

old_case1 = """        have h_q1_den_ge : q1.den ≥ q2.den + 1 := by omega
        have h_mul_le_nat : (p + 2) * q2.den ≤ q1.den * (p + 1) := by exact_mod_cast h_mul_le
        have h_calc1 : (p + 2) * q2.den = q2.den * (p + 1) + q2.den := by ring
        have h_calc2 : (q2.den + 1) * (p + 1) = q2.den * (p + 1) + (p + 1) := by ring
        have h_calc3 : (q2.den + 1) * (p + 1) ≤ q1.den * (p + 1) := Nat.mul_le_mul_right (p + 1) h_q1_den_ge
        have h_q2_den_le_p_nat : q2.den ≤ p + 1 := by omega
        sorry"""

new_case1 = """        have h_q1_den_ge : (q1.den : ℚ) ≥ (q2.den : ℚ) + 1 := by
          have h_le : q1.den ≥ q2.den + 1 := by omega
          exact_mod_cast h_le
        have hp_nonneg : (p : ℚ) ≥ 0 := by positivity
        have hq2_den_nonneg : (q2.den : ℚ) ≥ 0 := by positivity
        have h_q2_den_le_p : (q2.den : ℚ) ≤ (p : ℚ) + 1 := by nlinarith
        have h_q2_den_le_p_nat : q2.den ≤ p + 1 := by exact_mod_cast h_q2_den_le_p
        sorry"""

if old_case1 in content:
    content = content.replace(old_case1, new_case1)
    print("Replaced Case 1!")
else:
    print("Could not find Case 1!")

with open(path, 'w') as f:
    f.write(content)
