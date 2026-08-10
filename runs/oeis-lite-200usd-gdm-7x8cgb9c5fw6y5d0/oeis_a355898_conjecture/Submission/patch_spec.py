with open('/workspace/leanproject/Submission/Spec.lean', 'r') as f:
    spec_lines = f.readlines()

with open('/workspace/leanproject/Submission/test_gcd_proof11.lean', 'r') as f:
    proof_lines = f.readlines()

# Find the start of B_gcd in Spec.lean
start_spec = -1
for i, line in enumerate(spec_lines):
    if 'theorem B_gcd' in line:
        start_spec = i
        break

# Find the end of B_gcd in Spec.lean (where loop_eq_B_gen starts)
end_spec = -1
for i, line in enumerate(spec_lines):
    if 'theorem loop_eq_B_gen' in line:
        end_spec = i
        break

# Find the start of B_gcd in test_gcd_proof11.lean
start_proof = -1
for i, line in enumerate(proof_lines):
    if 'theorem B_gcd' in line:
        start_proof = i
        break

# Find the end of B_gcd in test_gcd_proof11.lean (blank line or next theorem, let's say up to the end of file or where it stops)
# Since the file ends shortly after B_gcd, let's find the 'omega' of B_gcd
end_proof = -1
for i in range(start_proof, len(proof_lines)):
    if 'omega' in proof_lines[i] and (i == len(proof_lines) - 1 or proof_lines[i+1].strip() == ''):
        end_proof = i + 1
        break

if start_spec != -1 and end_spec != -1 and start_proof != -1 and end_proof != -1:
    new_lines = spec_lines[:start_spec] + proof_lines[start_proof:end_proof] + ['\n\n'] + spec_lines[end_spec:]
    with open('/workspace/leanproject/Submission/Spec.lean', 'w') as f:
        f.writelines(new_lines)
    print("Patch applied successfully!")
else:
    print(f"Error locating lines: start_spec={start_spec}, end_spec={end_spec}, start_proof={start_proof}, end_proof={end_proof}")
