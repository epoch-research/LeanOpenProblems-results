import os
import subprocess

for root, dirs, files in os.walk("Submission"):
    for file in files:
        if file.endswith(".lean"):
            path = os.path.join(root, file)
            res = subprocess.run(["lake", "env", "lean", path], capture_output=True, text=True)
            if res.returncode == 0:
                # Check if it contains sorryAx
                if "sorryAx" not in res.stdout and "sorryAx" not in res.stderr:
                    print(f"SUCCESS: {path}")
                    print(res.stdout)
