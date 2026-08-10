# Read build_clean_spec.py
with open("/workspace/leanproject/Submission/build_clean_spec.py", "r") as f:
    lines = f.readlines()

new_lines = []
in_replace = False
for line in lines:
    if "p5_onwards = p5_onwards.replace" in line:
        in_replace = True
        continue
    if in_replace:
        if line.strip() == ")":
            in_replace = False
            continue
        elif "replace" in line:
            # safety net if parentheses count is mismatched
            in_replace = False
        else:
            continue
    new_lines.append(line)

with open("/workspace/leanproject/Submission/build_clean_spec.py", "w") as f:
    f.writelines(new_lines)

print("All p5_onwards replacements removed successfully!")
