import subprocess

with open("/workspace/leanproject/Submission/temp_test.lean", "r") as f:
    lines = f.readlines()

def try_compile(n):
    temp_path = "/workspace/leanproject/Submission/temp_short.lean"
    with open(temp_path, "w") as f:
        f.writelines(lines[:n])
    
    # Run lean on temp_short.lean
    res = subprocess.run(["lake", "env", "lean", temp_path], capture_output=True, text=True)
    if "Stack overflow detected" in res.stderr:
        return True # Overflowed
    else:
        return False # Did not overflow

# Let's check with some line counts
for lines_count in [615, 616, 617, 618, 619, 620]:
    overflow = try_compile(lines_count)
    print(f"Lines: {lines_count}, Overflow: {overflow}")
