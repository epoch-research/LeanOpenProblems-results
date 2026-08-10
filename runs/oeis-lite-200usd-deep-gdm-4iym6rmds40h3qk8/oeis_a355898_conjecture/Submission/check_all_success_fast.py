import os
import subprocess
import sys

files = [f for f in os.listdir('/workspace/leanproject/Submission') if f.endswith('.lean')]
files.sort()

for f in files:
    path = os.path.join('/workspace/leanproject/Submission', f)
    with open(path, 'r') as file_obj:
        content = file_obj.read()
    if 'sorry' in content:
        continue
    # Run lean on the file with a timeout of 15 seconds
    try:
        res = subprocess.run(['lake', 'env', 'lean', path], capture_output=True, text=True, timeout=15)
        if res.returncode == 0:
            print(f"SUCCESS: {f} compiled!", flush=True)
        else:
            # print(f"FAILED: {f}", flush=True)
            pass
    except subprocess.TimeoutExpired:
        print(f"TIMEOUT: {f}", flush=True)
