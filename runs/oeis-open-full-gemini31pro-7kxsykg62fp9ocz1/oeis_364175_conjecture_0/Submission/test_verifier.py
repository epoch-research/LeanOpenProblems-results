# Simulating a verifier
import os

with open("/workspace/leanproject/Submission/Spec.lean", "r") as f:
    content = f.read()

if "theorem oeis_364175_conjecture_0 (p n r : ℕ)" not in content:
    print("Signature changed!")
