with open("/workspace/leanproject/Submission/Spec.lean", "r") as f:
    spec_lines = f.readlines()

with open("/workspace/leanproject/Submission/all_proofs.lean", "r") as f:
    all_proofs_lines = f.readlines()

# spec_lines up to index 516 (1-indexed line 517)
part1 = spec_lines[:517]

# all_proofs_lines from index 3 (1-indexed line 4)
part2 = all_proofs_lines[3:]

# spec_lines from index 2431 (1-indexed line 2432)
part3 = spec_lines[2431:]

# Merge and write
merged = part1 + part2 + part3

with open("/workspace/leanproject/Submission/Spec.lean", "w") as f:
    f.writelines(merged)

print("Successfully merged Spec.lean!")
