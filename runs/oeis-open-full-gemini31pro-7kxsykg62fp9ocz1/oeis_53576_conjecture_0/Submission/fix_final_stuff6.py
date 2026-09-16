import sys
with open("/workspace/leanproject/Submission/Spec.lean.backup", "r") as f:
    orig = f.read()

with open("/workspace/leanproject/Submission/Spec.lean", "r") as f:
    text = f.read()

# Splice the text back to EXACTLY what was originally in Spec.lean, except for the theorem proof body.
# original had: theorem oeis_53576_conjecture_0 :\n    let N_idx : ℕ := 33\n    let N : ℕ := 2 ^ N_idx\n    let F33 : ℕ := Nat.fermatNumber N_idx\n    a N = if Nat.Prime F33 then F33 else 2 ^ (N + 1) := by\n  sorry\n\ntheorem oeis_53576_conjecture_0.disproof : ¬ (type_of% @oeis_53576_conjecture_0) := sorry\n

idx1 = orig.find("theorem oeis_53576_conjecture_0 :")
idx2 = orig.find("  sorry\n\ntheorem oeis_53576_conjecture_0.disproof") + len("  sorry\n")

my1 = text.find("  intros N_idx N F33")
my2 = text.find("theorem oeis_53576_conjecture_0.disproof")

final_text = orig[:idx1] + text[text.find("theorem oeis_53576_conjecture_0 :"):my1] + text[my1:my2] + orig[idx2:]

with open("/workspace/leanproject/Submission/Spec.lean", "w") as f:
    f.write(final_text)
