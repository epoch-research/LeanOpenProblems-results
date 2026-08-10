import re
import glob
import subprocess

files = sorted(glob.glob("/workspace/leanproject/Submission/TestPos*.lean"))
for f in files:
    with open(f, 'r') as fh:
        content = fh.read()
        # Find any theorem or def of type False
        if re.search(r'(theorem|def)\s+\w+\s*(:\s*False)?\s*:=', content):
            res = subprocess.run(["lean", f], capture_output=True, text=True)
            if res.returncode == 0:
                print(f"Candidate: {f}")
                # print any lines that look like a theorem of type False
                for line in content.splitlines():
                    if "False" in line and ("theorem" in line or "def" in line):
                        print("  ", line)
