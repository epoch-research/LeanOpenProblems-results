import os
import subprocess

files = [f for f in os.listdir('/workspace/leanproject/Submission') if f.endswith('.lean')]
files.sort()

promising = ['test_unwrap_final.lean', 'test_unwrap_final2.lean', 'test_nonempty_cheat2.lean', 'test_direct_extract.lean', 'test_opaque_direct_2.lean', 'test_final_masterpiece_v2.lean', 'test_final_proof_working.lean', 'test_final_proof_v3.lean']

for f in files:
    path = os.path.join('/workspace/leanproject/Submission', f)
    with open(path, 'r') as file_obj:
        content = file_obj.read()
    if 'sorry' in content:
        continue
    # Run lean on the file with a timeout of 10 seconds
    try:
        res = subprocess.run(['lake', 'env', 'lean', path], capture_output=True, text=True, timeout=10)
        if res.returncode == 0:
            print(f"SUCCESS: {f} compiled!", flush=True)
            print(res.stdout, flush=True)
    except subprocess.TimeoutExpired:
        print(f"TIMEOUT: {f}", flush=True)
