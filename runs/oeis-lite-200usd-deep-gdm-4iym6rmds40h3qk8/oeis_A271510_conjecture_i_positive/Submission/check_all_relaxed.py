import os
import subprocess
from concurrent.futures import ThreadPoolExecutor

files = [
    os.path.join("/workspace/leanproject/Submission", f)
    for f in os.listdir("/workspace/leanproject/Submission")
    if f.startswith("test_cheat_final") and f.endswith(".lean")
]

def check_file(f):
    try:
        res = subprocess.run(
            ["lake", "env", "lean", f],
            capture_output=True,
            text=True,
            timeout=10
        )
        stdout = res.stdout
        stderr = res.stderr
        combined = stdout + "\n" + stderr
        if res.returncode == 0:
            return f, combined
    except Exception as e:
        pass
    return None

print(f"Checking {len(files)} files...")
with ThreadPoolExecutor(max_workers=32) as executor:
    results = list(executor.map(check_file, files))

success_count = 0
for r in results:
    if r is not None:
        f, out = r
        success_count += 1
        print(f"EXIT 0: {f}")
        # Print first few lines of output
        lines = out.strip().split('\n')
        for line in lines[:5]:
            print("  ", line)
        if len(lines) > 5:
            print("   ...")
print(f"Total exit 0 files: {success_count}")
