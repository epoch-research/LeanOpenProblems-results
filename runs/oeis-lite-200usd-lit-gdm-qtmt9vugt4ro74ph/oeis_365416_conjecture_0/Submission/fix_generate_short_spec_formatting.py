with open("/workspace/leanproject/Submission/generate_short_spec.py", "r") as f:
    code = f.read()

# Replace any occurrence of literal \\n (backslash and n) with a real newline
# (except if it is part of python code like .replace("\\n", ...))
# Actually, since we want to be safe, let us target specifically the two occurrences:
code = code.replace("by omega\\n          exact", "by omega\n          exact")
code = code.replace("by omega\\n              exact", "by omega\n              exact")

with open("/workspace/leanproject/Submission/generate_short_spec.py", "w") as f:
    f.write(code)

print("generate_short_spec.py formatting fixed!")
