with open('/workspace/leanproject/Submission/Spec.lean', 'r') as f:
    lines = f.readlines()

for i, line in enumerate(lines):
    if "have hn_3 : 3 ≤ n := by omega" in line:
        lines[i] = "          have hn_3 : 3 ≤ n := by omega\n"
        # I should replace by `have hn_3 : 3 ≤ n := by omega` but wait, `omega` fails here because `n` is `p * (p-2)` which is hidden.
        # But we added `Hn_ge_15` which is `15 <= n` so `omega` should know it! Let's just use `Hn_ge_15`.
        lines[i] = "          have hn_3 : 3 ≤ n := by omega\n" # Wait, omega should know it if Hn_ge_15 is in local context. Why did it fail?
        # Let's write "          have hn_3 : 3 ≤ n := by linarith\n"
        lines[i] = "          have hn_3 : 3 ≤ n := by omega\n"
    if "rw [H_div1, ← H_sum_eq]" in line:
        lines[i] = "    rw [H_div1]\n"
    if "have H_sum_px : p - 1 ≤ ∑ x ∈ Icc (M - p + 3) M, padicValNat p (p * x) := sum_image_px p M hp hM_mod hM_ge" in line:
        lines[i] = line + "    rw [← H_sum_eq] at H_sum_px\n"

with open('/workspace/leanproject/Submission/Spec.lean', 'w') as f:
    f.writelines(lines)
