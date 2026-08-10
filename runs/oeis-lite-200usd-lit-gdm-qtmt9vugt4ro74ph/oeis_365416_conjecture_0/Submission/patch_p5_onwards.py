with open("/workspace/leanproject/Submission/build_clean_spec.py", "r") as f:
    code = f.read()

# Locate the replacements block
# From '# hq_mod (8) replacements' to the end of hp_mod (8) replacements
import re
pattern = r'# hq_mod \(8\) replacements.*?omega; omega\'\s+\)'

matches = re.findall(pattern, code, re.DOTALL)
print(f"Found {len(matches)} match(es) for p5_onwards replacements.")

# Replace with empty string (i.e. remove the replacements)
code = re.sub(pattern, '', code, flags=re.DOTALL)

with open("/workspace/leanproject/Submission/build_clean_spec.py", "w") as f:
    f.write(code)

print("Problematic replacements removed from build_clean_spec.py.")
