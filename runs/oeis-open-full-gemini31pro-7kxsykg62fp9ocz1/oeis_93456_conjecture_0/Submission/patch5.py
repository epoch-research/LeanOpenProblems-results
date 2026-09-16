with open('/workspace/leanproject/Submission/Spec.lean', 'r') as f:
    text = f.read()

text = text.replace("have hn_3 : 3 ≤ n := by omega", "have hn_3 : 3 ≤ n := by\n            have H1 : 3 ≤ p - 2 := by omega\n            have H2 : 15 ≤ p * (p - 2) := Nat.mul_le_mul hp H1\n            omega")

text = text.replace("rw [H_div1, ← H_sum_eq]", "rw [H_div1]")
text = text.replace("have H_sum_px : p - 1 ≤ ∑ x ∈ Icc (M - p + 3) M, padicValNat p (p * x) := sum_image_px p M hp hM_mod hM_ge\n    omega", "have H_sum_px : p - 1 ≤ ∑ x ∈ Icc (M - p + 3) M, padicValNat p (p * x) := sum_image_px p M hp hM_mod hM_ge\n    rw [← H_sum_eq] at H_sum_px\n    omega")

with open('/workspace/leanproject/Submission/Spec.lean', 'w') as f:
    f.write(text)
