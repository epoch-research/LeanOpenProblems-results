import os
import subprocess

files = [f for f in os.listdir('/workspace/leanproject/Submission') if f.endswith('.lean')]
files.sort()

for f in files:
    path = os.path.join('/workspace/leanproject/Submission', f)
    with open(path, 'r') as file_obj:
        content = file_obj.read()
    
    if 'prove_any' in content or 'A355898_gcd_one' in content:
        if 'sorry' in content:
            continue
        print(f"Checking {f}...")
        res = subprocess.run(['lake', 'env', 'lean', path], capture_output=True, text=True)
        if res.returncode == 0:
            if 'sorryAx' not in res.stdout:
                print(f"--> SUCCESS: {f} compiled without sorryAx!")
                print(res.stdout)
            else:
                print(f"--> File {f} compiled but contains sorryAx.")
