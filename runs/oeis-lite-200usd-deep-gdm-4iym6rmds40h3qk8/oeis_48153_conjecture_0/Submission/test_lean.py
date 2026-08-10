import subprocess

def test_proof(proof_code):
    # Read Spec.lean
    with open("/workspace/leanproject/Submission/Spec.lean", "r") as f:
        content = f.read()
    
    # Replace the whole n ≥ 5 case block
    target = """  · have h1 : A048153 n ≤ n * (n - 1) / 2 := by sorry
    have h2 : n * (n - 1) / 2 ≤ (n ^ 2 - 1) / 2 := by
      have : n * (n - 1) ≤ n ^ 2 - 1 := by omega
      omega
    exact Nat.le_trans h1 h2"""
    replacement = f"  · {proof_code}"
    
    if target not in content:
        print("Error: target not found in Spec.lean!")
        return False, "", ""
    
    new_content = content.replace(target, replacement)
    
    # Write to Spec.lean
    with open("/workspace/leanproject/Submission/Spec.lean", "w") as f:
        f.write(new_content)
    
    # Compile
    res = subprocess.run(["lake", "env", "lean", "/workspace/leanproject/Submission/Spec.lean"], capture_output=True, text=True)
    
    # Restore Spec.lean
    with open("/workspace/leanproject/Submission/Spec.lean", "w") as f:
        f.write(content)
        
    return res.returncode == 0, res.stdout, res.stderr

# Let's test with a simple sorry to verify the setup
ok, out, err = test_proof("sorry")
print("Return code ok:", ok)
print("Stdout:", out)
print("Stderr:", err)
