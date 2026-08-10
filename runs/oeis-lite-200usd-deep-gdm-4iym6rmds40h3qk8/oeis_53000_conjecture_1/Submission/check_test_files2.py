import subprocess
import glob

files = glob.glob("/workspace/leanproject/Submission/test_*.lean")
for f in files:
    res = subprocess.run(["lean", f], capture_output=True, text=True)
    if res.returncode == 0:
        # Check if the file contains the word "sorry"
        content = open(f).read()
        if "sorry" not in content and ("False" in content or "unsound" in content):
            print(f"NO_SORRY FILE WITH FALSE: {f}")
