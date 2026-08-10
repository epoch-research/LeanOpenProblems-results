import subprocess
import glob

files = glob.glob("/workspace/leanproject/Submission/test_*.lean")
for f in files:
    res = subprocess.run(["lean", f], capture_output=True, text=True)
    if res.returncode == 0:
        print(f"SUCCESS: {f}")
