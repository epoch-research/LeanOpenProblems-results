import os

path = "/workspace/leanproject/Submission/Spec.lean"
with open(path, 'r') as f:
    content = f.read()

start_marker = "lemma padicValRat_add_of_val_zero"
end_marker = "lemma padicValRat_nonneg_of_den_eq_one"

start_idx = content.find(start_marker)
end_idx = content.find(end_marker)

if start_idx == -1:
    print("Error: Could not find start marker!")
    exit(1)
if end_idx == -1:
    print("Error: Could not find end marker!")
    exit(1)

print(f"Start index: {start_idx}, End index: {end_idx}")

# We keep everything before start_idx and from end_idx onwards
new_content = content[:start_idx] + content[end_idx:]

with open(path, 'w') as f:
    f.write(new_content)

print("Successfully cleaned broken lemmas!")
