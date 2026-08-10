import os
import subprocess

files = [f for f in os.listdir('/workspace/leanproject/Submission') if f.endswith('.lean')]
files.sort()

for f in files:
    path = os.path.join('/workspace/leanproject/Submission', f)
    # Check if file mentions sorry
    with open(path, 'r') as file_obj:
        content = file_obj.read()
    
    # Run lean on the file
    res = subprocess.run(['lake', 'env', 'lean', path], capture_output=True, text=True)
    if res.returncode == 0:
        # Check if sorryAx is in stdout
        stdout = res.stdout
        stderr = res.stderr
        if 'sorryAx' not in stdout:
            print(f"SUCCESS: {f} compiled without sorryAx!")
            print(f"Axioms: {[line for line in stdout.splitlines() if 'depends on axioms' in line]}")
        else:
            print(f"File {f} compiled but contains sorryAx.")
    else:
        # Failed to compile
        pass
