import sys

N = 16384
N2 = N * N

v_vals = {}
for i in range(20):
    for s in range(10):
        fs = (10 * 16**s + 16 * 4**s + 10) // 9
        v = fs * 4**i
        idx = i * 10 + s
        v_vals[idx] = v

# Read blocking primes from generated Spec.lean
blocking_primes = {}
with open("/workspace/leanproject/Submission/Spec.lean") as f:
    lines = f.readlines()

in_match = False
for line in lines:
    if "def blocking_prime_by_idx" in line:
        in_match = True
        continue
    if in_match:
        if "| _ => 3" in line:
            break
        if "|" in line:
            parts = line.split("=>")
            idx = int(parts[0].replace("|", "").strip())
            p = int(parts[1].strip())
            blocking_primes[idx] = p

for idx in range(200):
    v = if_idx_199 = 1 if idx == 199 else v_vals[idx]
    p = blocking_primes[idx]
    
    if v >= N2:
        res = True
    else:
        diff = N2 - v
        res = (diff % p == 0) and (diff % (p*p) != 0)
        
    if not res:
        print(f"FAILED: idx {idx}, v = {v}, p = {p}, diff = {N2 - v}, diff % p = {diff % p}, diff % p^2 = {diff % (p*p)}")
