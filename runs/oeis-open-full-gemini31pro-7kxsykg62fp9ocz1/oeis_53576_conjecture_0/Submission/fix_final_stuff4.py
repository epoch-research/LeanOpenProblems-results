import sys
with open("/workspace/leanproject/Submission/Spec.lean", "r") as f:
    text = f.read()

text = text.replace("import Mathlib\nopen Nat Set Finset Classical", "import Mathlib\nopen Nat Set Finset Classical\n")

with open("/workspace/leanproject/Submission/Spec.lean", "w") as f:
    f.write(text)
