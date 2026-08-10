import sys

with open("/workspace/leanproject/Submission/output_vals.txt", "r") as f:
    text = f.read()

# Just take the first def
first_def = text.split("\n")[0]

with open("/workspace/leanproject/Submission/temp_decide.lean", "w") as f:
    f.write(first_def + "\n")
