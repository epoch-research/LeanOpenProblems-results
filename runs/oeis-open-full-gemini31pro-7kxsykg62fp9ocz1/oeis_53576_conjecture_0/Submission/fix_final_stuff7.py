import sys
with open("/workspace/leanproject/Submission/Spec.lean.backup", "r") as f:
    orig = f.read()

with open("/workspace/leanproject/Submission/Spec.lean", "r") as f:
    text = f.read()

idx1 = orig.find("theorem oeis_53576_conjecture_0 :")
idx2 = orig.find("theorem oeis_53576_conjecture_0.disproof")

my1 = text.find("  intros N_idx N F33")
my2 = text.find("FormalConjectures.Util.ProblemImports")

final_text = orig[:idx1] + text[text.find("theorem oeis_53576_conjecture_0 :"):my1] + text[my1:my2] + orig[idx2:]
final_text = final_text.replace("if F33.Prime then", "if Nat.Prime F33 then")
final_text = final_text.replace("hPrime : F33.Prime", "hPrime : Nat.Prime F33")
final_text = final_text.replace("have hF33_prime : F33.Prime :=", "have hF33_prime : Nat.Prime F33 :=")

with open("/workspace/leanproject/Submission/Spec.lean", "w") as f:
    f.write(final_text)
