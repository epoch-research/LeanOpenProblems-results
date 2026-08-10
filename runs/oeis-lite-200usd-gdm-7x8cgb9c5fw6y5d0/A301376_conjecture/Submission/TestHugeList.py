import subprocess
import time

primes = []
candidate = 3
while len(primes) < 6401:
    # check if candidate is prime
    is_p = True
    for p in primes:
        if p*p > candidate:
            break
        if candidate % p == 0:
            is_p = False
            break
    if is_p:
        primes.append(candidate)
    candidate += 2

lines = [
    "import FormalConjectures.Util.ProblemImports",
    "set_option maxRecDepth 10000",
    ""
]

# split primes into sublists of size 100
chunk_size = 100
sublists = [primes[i:i + chunk_size] for i in range(0, len(primes), chunk_size)]

for idx, sub in enumerate(sublists):
    lines.append(f"def sublist_{idx} : List ℕ := [{', '.join(map(str, sub))}]")

# concatenate them
lines.append(f"def huge_primes_list : List ℕ := " + " ++ ".join(f"sublist_{idx}" for idx in range(len(sublists))))
lines.append("")
lines.append("lemma huge_primes_prime : ∀ p ∈ huge_primes_list, Nat.Prime p := by")
lines.append("  decide")

with open("/workspace/leanproject/Submission/TestHugeList.lean", "w") as f:
    f.write("\n".join(lines))
    
start = time.time()
res = subprocess.run(["lake", "env", "lean", "/workspace/leanproject/Submission/TestChunk.lean"], capture_output=True, text=True)
end = time.time()
print(f"Time to compile TestChunk: {end - start:.2f}s")

start = time.time()
res = subprocess.run(["lake", "env", "lean", "/workspace/leanproject/Submission/TestHugeList.lean"], capture_output=True, text=True)
end = time.time()

if res.returncode == 0:
    print(f"huge_primes_list (size 6401): SUCCESS! Time: {end - start:.2f}s")
else:
    print(f"huge_primes_list (size 6401): FAILED! Error:\n{res.stdout}\n{res.stderr}")
