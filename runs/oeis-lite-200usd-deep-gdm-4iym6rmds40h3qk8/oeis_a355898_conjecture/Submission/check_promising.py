import os
import subprocess

files = [f for f in os.listdir('/workspace/leanproject/Submission') if f.endswith('.lean')]
files.sort()

promising = []
for f in files:
    path = os.path.join('/workspace/leanproject/Submission', f)
    with open(path, 'r') as file_obj:
        content = file_obj.read()
    if 'A355898_gcd_one' in content and 'sorry' not in content:
        promising.append(f)

print(f"Promising files: {promising}")
# Let's check them one by one
for f in promising:
    path = os.path.join('/workspace/leanproject/Submission', f)
    print(f"Checking {f}...")
    res = subprocess.run(['lake', 'env', 'lean', path], capture_output=True, text=True)
    if res.returncode == 0:
        if 'sorryAx' not in res.stdout:
            print(f"--> SUCCESS: {f} compiled without sorryAx!")
            print(res.stdout)
            break
        else:
            print(f"--> File {f} compiled but contains sorryAx.")
    else:
        print(f"--> File {f} failed to compile.")
