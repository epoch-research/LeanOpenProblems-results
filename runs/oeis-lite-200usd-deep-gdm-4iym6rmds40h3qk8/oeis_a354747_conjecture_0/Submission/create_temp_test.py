with open("/workspace/leanproject/Submission/Spec.lean", "r") as f:
    content = f.read()

# Find the end of W_all_eq_one proof
marker = "lemma W_all_eq_one : get_W_all alpha_const = 1 := by decide"
idx = content.find(marker)

if idx == -1:
    print("Marker not found!")
else:
    # Include the marker and the newline
    short_content = content[:idx + len(marker)] + "\n"
    with open("/workspace/leanproject/Submission/temp_test.lean", "w") as f:
        f.write(short_content)
    print("temp_test.lean written!")
