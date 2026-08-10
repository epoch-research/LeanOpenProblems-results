import subprocess
import glob

files = sorted(glob.glob("/workspace/leanproject/Submission/TestPos*.lean"))
for f in files:
    res = subprocess.run(["lean", f], capture_output=True, text=True)
    if res.returncode == 0:
        with open(f, 'r') as fh:
            content = fh.read()
            if "sorry" not in content and "False" in content:
                print(f"COMPLETELY TRUE PROOF OF FALSE IN: {f}")
