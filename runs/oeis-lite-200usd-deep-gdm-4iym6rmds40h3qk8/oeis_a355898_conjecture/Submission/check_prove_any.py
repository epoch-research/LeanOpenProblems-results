import os
import subprocess

files = [f for f in os.listdir('/workspace/leanproject/Submission') if f.endswith('.lean')]
files.sort()

for f in files:
    path = os.path.join('/workspace/leanproject/Submission', f)
    with open(path, 'r') as file_obj:
        content = file_obj.read()
    
    if 'prove_any' in content:
        res = subprocess.run(['lake', 'env', 'lean', path], capture_output=True, text=True)
        if res.returncode == 0 and 'sorry' not in content:
            print(f"SUCCESS: {f} compiles and has prove_any!")
            print(res.stdout)
