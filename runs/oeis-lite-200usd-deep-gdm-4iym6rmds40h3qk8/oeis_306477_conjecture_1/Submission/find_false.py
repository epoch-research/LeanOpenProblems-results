import subprocess
import glob

files = [
    "/workspace/leanproject/Submission/TestPos100.lean",
    "/workspace/leanproject/Submission/TestPos102.lean",
    "/workspace/leanproject/Submission/TestPos109.lean",
    "/workspace/leanproject/Submission/TestPos110.lean",
    "/workspace/leanproject/Submission/TestPos111.lean",
    "/workspace/leanproject/Submission/TestPos112.lean",
    "/workspace/leanproject/Submission/TestPos113.lean",
    "/workspace/leanproject/Submission/TestPos115.lean",
    "/workspace/leanproject/Submission/TestPos118.lean",
    "/workspace/leanproject/Submission/TestPos120.lean",
    "/workspace/leanproject/Submission/TestPos200.lean",
    "/workspace/leanproject/Submission/TestPos201.lean",
    "/workspace/leanproject/Submission/TestPos202.lean",
    "/workspace/leanproject/Submission/TestPos203.lean",
    "/workspace/leanproject/Submission/TestPos205.lean",
    "/workspace/leanproject/Submission/TestPos208.lean",
    "/workspace/leanproject/Submission/TestPos215.lean",
    "/workspace/leanproject/Submission/TestPos216.lean",
    "/workspace/leanproject/Submission/TestPos228.lean",
    "/workspace/leanproject/Submission/TestPos232.lean",
    "/workspace/leanproject/Submission/TestPos234.lean",
    "/workspace/leanproject/Submission/TestPos53.lean",
    "/workspace/leanproject/Submission/TestPos54.lean",
    "/workspace/leanproject/Submission/TestPos62.lean",
    "/workspace/leanproject/Submission/TestPos63.lean",
    "/workspace/leanproject/Submission/TestPos64.lean",
    "/workspace/leanproject/Submission/TestPos65.lean",
    "/workspace/leanproject/Submission/TestPos66.lean",
    "/workspace/leanproject/Submission/TestPos71.lean",
    "/workspace/leanproject/Submission/TestPos74.lean",
    "/workspace/leanproject/Submission/TestPos77.lean",
    "/workspace/leanproject/Submission/TestPos80.lean",
    "/workspace/leanproject/Submission/TestPos81.lean",
    "/workspace/leanproject/Submission/TestPos84.lean",
    "/workspace/leanproject/Submission/TestPos85.lean",
    "/workspace/leanproject/Submission/TestPos88.lean",
    "/workspace/leanproject/Submission/TestPos92.lean",
    "/workspace/leanproject/Submission/TestPos96.lean",
    "/workspace/leanproject/Submission/TestPos97.lean",
    "/workspace/leanproject/Submission/TestPos99.lean"
]

for f in files:
    with open(f, "r") as fh:
        content = fh.read()
        if "False" in content or "false" in content:
            # Let's see if it's proving False or has a theorem of type False
            if "theorem" in content and "False" in content:
                print(f"Candidate: {f}")
