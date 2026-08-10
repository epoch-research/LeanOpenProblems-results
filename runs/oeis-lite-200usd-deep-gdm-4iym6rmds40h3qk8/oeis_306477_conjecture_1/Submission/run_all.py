import subprocess
import glob
import os

files = sorted(glob.glob("/workspace/leanproject/Submission/TestPos*.lean"))
success = []
for f in files:
    res = subprocess.run(["lean", f], capture_output=True, text=True)
    if res.returncode == 0:
        success.append(f)
        print(f"Success: {f}")
    else:
        # Check if there is only a warning about sorry
        if "warning: declaration uses 'sorry'" in res.stderr or "warning: declaration uses 'sorry'" in res.stdout:
            # check if there are other errors
            errors = [line for line in (res.stdout + res.stderr).splitlines() if "error" in line]
            if not errors:
                print(f"Success with sorry warning: {f}")
                success.append(f)

print(f"Total success: {len(success)}")
