import subprocess
import glob
import re

files = glob.glob("/workspace/leanproject/Submission/test_*.lean")
for f in files:
    content = open(f).read()
    # Find all theorem or def names
    matches = re.findall(r"(?:theorem|def|lemma)\s+([a-zA-Z0-9_'\?]+)", content)
    if not matches:
        continue
    
    # Try checking each name
    for name in matches:
        # We append "#check <name>" and compile
        test_content = content + f"\n#check {name}\n"
        res = subprocess.run(["lean", "-"], input=test_content, capture_output=True, text=True)
        if res.returncode == 0:
            # Parse type of name from stdout (it prints "<name> : <type>")
            lines = res.stdout.strip().split("\n")
            for line in lines:
                if line.startswith(f"{name} :") and "False" in line:
                    print(f"FOUND PROOF OF FALSE: {f} -> {name} : {line}")
