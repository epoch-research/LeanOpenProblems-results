import subprocess
import time

def test_size(c):
    lines = [
        "import FormalConjectures.Util.ProblemImports",
        "set_option maxRecDepth 1000000",
        "set_option maxHeartbeats 2000000",
        "",
        "def test_func (v : ℕ) : ℕ :=",
        "  match v with"
    ]
    for i in range(1, c + 1):
        lines.append(f"  | {i*4} => 3")
    lines.append("  | _ => 3")
    lines.append("")
    lines.append("lemma test_func_prime (v : ℕ) : Nat.Prime (test_func v) :=")
    lines.append("  by unfold test_func; split <;> decide")
    
    with open("/workspace/leanproject/Submission/TestChunk.lean", "w") as f:
        f.write("\n".join(lines))
        
    start = time.time()
    res = subprocess.run(["lake", "env", "lean", "/workspace/leanproject/Submission/TestChunk.lean"], capture_output=True, text=True)
    end = time.time()
    
    if res.returncode == 0:
        print(f"Size {c}: SUCCESS! Time: {end - start:.2f}s")
    else:
        print(f"Size {c}: FAILED! Error:\n{res.stdout}\n{res.stderr}")

for c in [500, 1000]:
    test_size(c)
