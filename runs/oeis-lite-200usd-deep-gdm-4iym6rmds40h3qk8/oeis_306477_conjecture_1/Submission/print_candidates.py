import subprocess

candidates = [
    "/workspace/leanproject/Submission/TestPos110.lean",
    "/workspace/leanproject/Submission/TestPos112.lean",
    "/workspace/leanproject/Submission/TestPos113.lean",
    "/workspace/leanproject/Submission/TestPos115.lean",
    "/workspace/leanproject/Submission/TestPos120.lean",
    "/workspace/leanproject/Submission/TestPos215.lean",
    "/workspace/leanproject/Submission/TestPos53.lean",
    "/workspace/leanproject/Submission/TestPos74.lean",
    "/workspace/leanproject/Submission/TestPos88.lean",
    "/workspace/leanproject/Submission/TestPos99.lean"
]

for c in candidates:
    print(f"--- File: {c} ---")
    with open(c, "r") as fh:
        lines = fh.readlines()
        for line in lines:
            if "theorem" in line or "def" in line:
                print("  ", line.strip())
