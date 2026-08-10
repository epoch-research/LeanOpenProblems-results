import math
import sys
from sympy import isprime

n0 = 2034574569411661048898610203059339310825150502849021143319870323451393040605379736020615137843352467506831716518098181133819921266057656805282384207565721754733253485197363751816948460329
n2 = n0*n0

used_primes = [11, 31, 19, 43, 127, 23, 59, 47, 67, 79, 103, 163, 71, 83, 107, 131, 167, 191, 211, 223, 227, 311, 331, 139, 151, 179, 199, 239, 251, 263, 271, 283, 307, 347, 367, 379, 383, 419, 431, 439, 443, 463]
all_primes = [3, 7] + used_primes

# We want to find the maximum k
# 4^k <= n2 => k <= 305
K_MAX = 305

# We will generate the 1D array of size (K_MAX + 1) * (K_MAX + 2) // 2
cert_array = []
total_elements = (K_MAX + 1) * (K_MAX + 2) // 2

print(f"Total elements to generate: {total_elements}")

for k in range(K_MAX + 1):
    for u in range(k + 1):
        if u == 0:
            if k == 0:
                v = 1
            else:
                # dummy value for u=0, k>=1
                cert_array.append(11)
                continue
        else:
            # v = 4^(u-1) * (10 * 16^(k-u) + 16 * 4^(k-u) + 10) // 9
            s = k - u
            i = u - 1
            v = 4**i * (10 * 16**s + 16 * 4**s + 10) // 9
            
        # Find the prime that blocks v
        found = False
        for p in all_primes:
            if (n2 - v) % p == 0 and (n2 - v) % (p*p) != 0:
                cert_array.append(p)
                found = True
                break
        if not found:
            print(f"ERROR: Could not find blocking prime for k={k}, u={u}, v={v}")
            sys.exit(1)

print(f"Successfully generated cert_array of size {len(cert_array)}")
# Write the array to a file in Lean format
with open("/workspace/leanproject/Submission/cert_array.txt", "w") as f:
    f.write("#[")
    f.write(", ".join(map(str, cert_array)))
    f.write("]")
print("Wrote cert_array to /workspace/leanproject/Submission/cert_array.txt")
