import sys
sys.set_int_max_str_digits(1000000)
import time

t0 = time.time()
N = 2 * 100943 * 3**39101 - 1

class R:
    def __init__(self, u, v):
        self.u = u % N
        self.v = v % N
    
    def __mul__(self, other):
        return R(self.u * other.u + 3 * self.v * other.v, self.u * other.v + self.v * other.u)

    def __sub__(self, other):
        return R(self.u - other.u, self.v - other.v)
    
    def inv(self):
        norm = (self.u**2 - 3 * self.v**2) % N
        inv_norm = pow(norm, -1, N)
        return R(self.u * inv_norm, -self.v * inv_norm)

def power(a, n):
    res = R(1, 0)
    b = bin(n)[2:]
    for bit in b:
        res = res * res
        if bit == '1':
            res = res * a
    return res

alpha = R(2, 1)

M2 = 100943 * 3**39101
M3 = 2 * 100943 * 3**39100
Mp = 2 * 3**39101

v2 = power(alpha, M2)
v3 = power(alpha, M3)
vp = power(alpha, Mp)

inv2 = (v2 - R(1, 0)).inv()
inv3 = (v3 - R(1, 0)).inv()
invp = (vp - R(1, 0)).inv()

with open("/workspace/leanproject/Submission/TestCertVals.lean", "w") as f:
    f.write("import FormalConjectures.Util.ProblemImports\n")
    f.write("namespace R\n")
    f.write("def my_N : ℕ := 2 * 100943 * 3^39101 - 1\n")
    f.write(f"def inv2_u : ℕ := {inv2.u}\n")
    f.write(f"def inv2_v : ℕ := {inv2.v}\n")
    f.write(f"def inv3_u : ℕ := {inv3.u}\n")
    f.write(f"def inv3_v : ℕ := {inv3.v}\n")
    f.write(f"def invp_u : ℕ := {invp.u}\n")
    f.write(f"def invp_v : ℕ := {invp.v}\n")
    f.write("end R\n")

print(f"Done in {time.time()-t0}s")
