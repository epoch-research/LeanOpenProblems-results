# Read write_pillai_final.py to extract lines for q = 29, 83, 227
with open("/workspace/leanproject/Submission/write_pillai_final.py", "r") as f:
    orig_lines = f.readlines()

# Extract the block for r == 227 (lines 758 to 875, 1-indexed)
q227_block = []
for line in orig_lines[757:875]:
    # Evaluate `{r}` as `227`
    evaluated = line.replace("{r}", "227").strip()
    q227_block.append("    " + evaluated)

# Extract the block for r == 29 (lines 878 to 1038, 1-indexed)
q29_block = []
for line in orig_lines[877:1038]:
    # Evaluate `{r}` as `29`
    evaluated = line.replace("{r}", "29").strip()
    q29_block.append("    " + evaluated)

# Extract the block for r == 83 (lines 1041 to 1149, 1-indexed)
q83_block = []
for line in orig_lines[1040:1149]:
    # Evaluate `{r}` as `83`
    evaluated = line.replace("{r}", "83").strip()
    q83_block.append("    " + evaluated)

# Join the blocks
q29_text = "\n".join(q29_block)
q83_text = "\n".join(q83_block)
q227_text = "\n".join(q227_block)

# Read build_clean_spec.py
with open("/workspace/leanproject/Submission/build_clean_spec.py", "r") as f:
    code = f.read()

# Define the target patterns to replace in build_clean_spec.py
# 1. q = 29 block is lines 367 to 414
# Let's find the boundaries of q = 29 block in build_clean_spec.py
import re

pattern_q29 = r'    p3_code\.append\("        by_cases hq29 : q = 29"\).*?interval_cases hf_mod_val : f % 6 <;> revert h_zmod <;> decide"\)'
pattern_q83 = r'    p3_code\.append\("        by_cases hq83 : q = 83"\).*?interval_cases hf_mod_val : f % 6 <;> revert h_zmod <;> decide"\)'
pattern_q227 = r'    p3_code\.append\("        by_cases hq227 : q = 227"\).*?interval_cases hf_mod_val : f % 6 <;> revert h_zmod <;> decide"\)'

# Let's print matches to verify
match29 = re.search(pattern_q29, code, re.DOTALL)
match83 = re.search(pattern_q83, code, re.DOTALL)
match227 = re.search(pattern_q227, code, re.DOTALL)

if match29 and match83 and match227:
    print("All three blocks successfully matched!")
    # Replace the blocks
    code = re.sub(pattern_q29, q29_text, code, flags=re.DOTALL)
    code = re.sub(pattern_q83, q83_text, code, flags=re.DOTALL)
    code = re.sub(pattern_q227, q227_text, code, flags=re.DOTALL)
    
    with open("/workspace/leanproject/Submission/build_clean_spec.py", "w") as f:
        f.write(code)
    print("build_clean_spec.py successfully patched with correct base case proofs!")
else:
    print(f"Match status: q29={bool(match29)}, q83={bool(match83)}, q227={bool(match227)}")
