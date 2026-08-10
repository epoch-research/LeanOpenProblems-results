import os
import subprocess

files = [
    f for f in os.listdir("/workspace/leanproject/Submission")
    if f.startswith("test_cheat_final") and f.endswith(".lean")
]

for f in sorted(files):
    path = os.path.join("Submission", f)
    # read file
    with open(os.path.join("/workspace/leanproject", path), "r") as file:
        content = file.read()
    if "sorry" in content:
        continue
    try:
        res = subprocess.run(
            ["lake", "env", "lean", path],
            capture_output=True,
            text=True,
            timeout=10,
            cwd="/workspace/leanproject"
        )
        if res.returncode == 0:
            # check if there's any warning about sorry
            combined = res.stdout + "\n" + res.stderr
            if "sorry" not in combined and "sorryAx" not in combined:
                print(f"!!! SUCCESS NO SORRY: {f} !!!")
                print(content)
                print("="*80)
    except Exception as e:
        pass
