import subprocess
import time

def test_size_indices(c):
    lines = [
        "import FormalConjectures.Util.ProblemImports",
        "",
        "def test_func (i s : ℕ) : ℕ :=",
        "  match i, s with"
    ]
    for idx in range(1, c + 1):
        i_val = idx % 160
        s_val = idx // 160
        lines.append(f"  | {i_val}, {s_val} => 3")
    lines.append("  | _, _ => 3")
    lines.append("")
    lines.append("lemma test_func_prime (i s : ℕ) : Nat.Prime (test_func i s) :=")
    lines.append("  by unfold test_func; split <;> decide")
    
    with open("/workspace/leanproject/Submission/TestChunkIndices.lean", "w") as f:
        f.write("\n".join(lines))
        
    start = time.time()
    res = subprocess.run(["lake", "env", "lean", "/workspace/leanproject/Submission/TestChunkIndices.lean"], capture_output=True, text=True)
    end = time.time()
    
    if res.returncode == 0:
        print(f"Size {c}: SUCCESS! Time: {end - start:.2f}s")
    else:
        print(f"Size {c}: FAILED! Error:\n{res.stdout}\n{res.stderr}")

test_size_indices(100)
