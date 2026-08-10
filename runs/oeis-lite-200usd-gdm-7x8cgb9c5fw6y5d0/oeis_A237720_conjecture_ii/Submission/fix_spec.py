import re

with open('/workspace/leanproject/Submission/Spec.lean', 'r') as f:
    content = f.read()

# Replace hardcoded base case pattern
old_pattern = '· intro hc; rw [h_n] at hc; norm_num at hc; exact hc'
new_pattern = '· intro hc; rw [h_n] at *; norm_num at *'
assert old_pattern in content, "Could not find the old pattern in Spec.lean!"
content = content.replace(old_pattern, new_pattern)

# Locate the induction step block around lines 1055-1071
old_induction_block = """      refine ⟨hp'_prime, hp'_lt_n1, ?_, ?_, ?_, ?_⟩
      · rwa [h_eq]
      · rw [h_eq]
        omega
      · intro hc
        omega
      · intro hc
        rw [h_eq] at hc
        have hp_le_4S : p ≤ 4 * (S - 1) - 2 := by
          have h_sqrt : sqrt (n + p) = S - 1 := h_sqrt_eq
          have h_cond_premise : sqrt (n + p) ≥ 12 := by omega
          rw [h_sqrt] at h_cond2
          exact h_cond2 h_cond_premise
        have h_div : 2 * ((p - 1) / 2) ≤ p - 1 := Nat.mul_div_le (p - 1) 2
        have hp'_le_p_sub_one : p' ≤ p - 1 := le_trans hp'_le h_div
        omega"""

new_induction_block = """      refine ⟨hp'_prime, hp'_lt_n1, ?_, ?_, ?_, ?_⟩
      · rwa [h_eq]
      · rw [h_eq]
        omega
      · intro hc
        have h_div_le : (p - 1) / 2 ≤ 1 := by omega
        have h_mod : (p - 1) % 2 < 2 := Nat.mod_lt (p - 1) (by decide)
        have h_decomp : p - 1 = 2 * ((p - 1) / 2) + (p - 1) % 2 := (Nat.div_add_mod (p - 1) 2).symm
        omega
      · intro hc
        rw [h_eq] at hc
        have hp_le_4S : p ≤ 4 * (S - 1) - 2 := by
          have h_sqrt : sqrt (n + p) = S - 1 := h_sqrt_eq
          have h_cond_premise : sqrt (n + p) ≥ 12 := by omega
          rw [h_sqrt] at h_cond2 h_cond_premise
          exact h_cond2 h_cond_premise
        have h_div : 2 * ((p - 1) / 2) ≤ p - 1 := Nat.mul_div_le (p - 1) 2
        have hp'_le_p_sub_one : p' ≤ p - 1 := le_trans hp'_le h_div
        omega"""

assert old_induction_block in content, "Could not find the old induction block in Spec.lean!"
content = content.replace(old_induction_block, new_induction_block)

with open('/workspace/leanproject/Submission/Spec.lean', 'w') as f:
    f.write(content)

print("Replacement complete successfully!")
