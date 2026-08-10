import subprocess
import time

def test_size_seq(c):
    lines = [
        "import FormalConjectures.Util.ProblemImports",
        "",
        "def test_func (v : ℕ) : ℕ :=",
        "  match v with"
    ]
    for i in range(1, c + 1):
        lines.append(f"  | {i} => 3")
    lines.append("  | _ => 3")
    lines.append("")
    lines.append("lemma test_func_prime (v : ℕ) : Nat.Prime (test_func v) :=")
    lines.append("  by")
    lines.append("    unfold test_func")
    for _ in range(c + 1):
        lines.append("    split")
        lines.append("    · decide")
    lines.append("    decide")
    
    with open("/workspace/leanproject/Submission/TestChunkSeq.lean", "w") as f:
        f.write("\n".join(lines))
        
    start = time.time()
    res = subprocess.run(["lake", "env", "lean", "/workspace/leanproject/Submission/TestChunkSeq.lean"], capture_output=True, text=True)
    end = time.time()
    
    if res.returncode == 0:
        print(f"Size {c} (sequential): SUCCESS! Time: {end - start:.2f}s")
    else:
        print(f"Size {c} (sequential): FAILED! Error:\n{res.stdout}\n{res.stderr}")

test_size_seq(100)
