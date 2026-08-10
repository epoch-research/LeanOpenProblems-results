import os
import subprocess
from multiprocessing import Pool

def check_file(f):
    if not f.endswith(".lean"):
        return None
    path = os.path.join("/workspace/leanproject/Submission", f)
    # run lake env lean
    res = subprocess.run(["lake", "env", "lean", path], capture_output=True, text=True)
    if res.returncode == 0:
        # Check if there are any warnings/errors
        # (res.stdout might contain warnings, but returncode is 0)
        return path, res.stdout, res.stderr
    return None

def main():
    files = os.listdir("/workspace/leanproject/Submission")
    print(f"Checking {len(files)} files on 32 cores...")
    with Pool(32) as p:
        results = p.map(check_file, files)
    
    successes = [r for r in results if r is not None]
    print(f"Found {len(successes)} successful files:")
    for path, stdout, stderr in successes:
        print(f"SUCCESS: {path}")
        if stdout:
            print(f"Stdout:\n{stdout}")
        if stderr:
            print(f"Stderr:\n{stderr}")

if __name__ == '__main__':
    main()
