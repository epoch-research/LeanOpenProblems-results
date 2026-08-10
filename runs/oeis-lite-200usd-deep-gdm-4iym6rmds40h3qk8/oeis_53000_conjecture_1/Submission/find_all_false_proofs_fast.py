import subprocess
import glob
import re
import os
from multiprocessing import Pool

def check_file(f):
    content = open(f).read()
    if "sorry" in content:
        return None
        
    # Let us check if there is unsound or false_proof or girard or anything
    # We can just look for theorem or def of type False
    # To be extremely precise, we can append a command to print all axioms of the suspects,
    # or just run lake env lean on the file.
    # If the file compiles cleanly (exit code 0), let us search for "False" in the file.
    # If "False" is not in the file, it cannot prove False.
    if "False" not in content and "false" not in content:
        return None
        
    res = subprocess.run(["lake", "env", "lean", f], capture_output=True, text=True)
    if res.returncode == 0:
        # Check if there is any theorem or def in the file
        matches = re.findall(r"(?:theorem|def|lemma)\s+([a-zA-Z0-9_'\?]+)", content)
        for name in matches:
            # Check type by writing to a temp file and running lake env lean
            temp_name = f"{f}_temp_check.lean"
            with open(temp_name, "w") as tf:
                tf.write(content + f"\n#check {name}\n")
            res2 = subprocess.run(["lake", "env", "lean", temp_name], capture_output=True, text=True)
            if os.path.exists(temp_name):
                os.remove(temp_name)
            if res2.returncode == 0:
                for line in res2.stdout.strip().split("\n"):
                    if "False" in line and (line.startswith(f"{name} :") or f" {name} " in line):
                        return f, name, line
    return None

def main():
    files = glob.glob("/workspace/leanproject/Submission/test_*.lean")
    print(f"Checking {len(files)} files in parallel...", flush=True)
    with Pool(32) as p:
        results = p.map(check_file, files)
        for r in results:
            if r is not None:
                print(f"FOUND PROOF OF FALSE: file={r[0]}, name={r[1]}, type={r[2]}")

if __name__ == "__main__":
    main()
