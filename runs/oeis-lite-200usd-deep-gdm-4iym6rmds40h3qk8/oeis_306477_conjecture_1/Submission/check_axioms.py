import subprocess

# Let's compile Spec.lean and print its axioms using some lean command or python
# Actually we can check axioms using Lean code:
# `#print axioms oeis_306477_conjecture_1`
# Let's create a temporary Lean file that imports Spec and prints the axioms.

with open("/workspace/leanproject/Submission/check_axioms.lean", "w") as f:
    f.write("import Submission.Spec\n#print axioms oeis_306477_conjecture_1\n")

res = subprocess.run(["lake", "env", "lean", "/workspace/leanproject/Submission/check_axioms.lean"], capture_output=True, text=True)
print(res.stdout)
print(res.stderr)
