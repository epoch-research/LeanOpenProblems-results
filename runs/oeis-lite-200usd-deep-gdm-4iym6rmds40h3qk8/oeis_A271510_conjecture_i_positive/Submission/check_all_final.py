import os
import subprocess
from concurrent.futures import ThreadPoolExecutor

files = [
    f for f in os.listdir("/workspace/leanproject/Submission")
    if f.endswith(".lean")
]

def check_file(f):
    path = os.path.join("Submission", f)
    try:
        res = subprocess.run(
            ["lake", "env", "lean", path],
            capture_output=True,
            text=True,
            timeout=15,
            cwd="/workspace/leanproject"
        )
        stdout = res.stdout
        stderr = res.stderr
        combined = stdout + "\n" + stderr
        if res.returncode == 0:
            if "error:" not in combined and "warning:" not in combined and "sorry" not in combined and "sorryAx" not in combined:
                return f, combined
    except Exception as e:
        pass
    return None

print(f"Checking {len(files)} files...")
with ThreadPoolExecutor(max_workers=16) as executor:
    results = list(executor.map(check_file, files))

for r in results:
    if r is not None:
        print(f"FOUND SUCCESS: {r[0]}")
        print(r[1])
        print("="*40)
