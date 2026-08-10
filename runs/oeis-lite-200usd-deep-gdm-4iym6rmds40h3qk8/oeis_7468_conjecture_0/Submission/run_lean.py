import subprocess
import sys

def run_lean(filename):
    print(f"Running Lean on {filename}...")
    proc = subprocess.Popen(
        ["lake", "env", "lean", filename],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True
    )
    try:
        # Wait for a bit and read output
        stdout, stderr = proc.communicate(timeout=5)
        print("STDOUT:")
        print(stdout)
        print("STDERR:")
        print(stderr)
    except subprocess.TimeoutExpired:
        print("Lean timed out! Killing...")
        proc.kill()
        stdout, stderr = proc.communicate()
        print("STDOUT SO FAR:")
        print(stdout)
        print("STDERR SO FAR:")
        print(stderr)

if __name__ == "__main__":
    if len(sys.argv) > 1:
        run_lean(sys.argv[1])
    else:
        print("Usage: python run_lean.py <filename>")
