import subprocess
import glob

files = sorted(glob.glob("/workspace/leanproject/Submission/TestPos*.lean"))
no_sorry = []
for f in files:
    res = subprocess.run(["lean", f], capture_output=True, text=True)
    if res.returncode == 0:
        output = res.stdout + res.stderr
        if "sorry" not in output and "warning" not in output:
            no_sorry.append(f)
            print(f"Absolutely Clean: {f}")

print(f"Total clean: {len(no_sorry)}")
