import sys
sys.set_int_max_str_digits(1000000)

N = 2 * 100943 * 3**39101 - 1

class R:
    def __init__(self, u, v):
        self.u = u % N
        self.v = v % N
    
    def __mul__(self, other):
        return R(self.u * other.u + 3 * self.v * other.v, self.u * other.v + self.v * other.u)

    def __sub__(self, other):
        return R(self.u - other.u, self.v - other.v)
    
    def ext_gcd(self, a, b):
        if a == 0:
            return b, 0, 1
        gcd, x1, y1 = self.ext_gcd(b % a, a)
        x = y1 - (b // a) * x1
        y = x1
        return gcd, x, y

    def inv(self):
        # We need the inverse of (u + v*sqrt(3))
        # Norm is u^2 - 3v^2
        norm = (self.u**2 - 3 * self.v**2) % N
        gcd, x, y = self.ext_gcd(norm, N)
        if gcd != 1:
            raise Exception("Not invertible!")
        inv_norm = x % N
        return R(self.u * inv_norm, -self.v * inv_norm)

def power(a, n):
    res = R(1, 0)
    while n > 0:
        if n % 2 == 1:
            res = res * a
        a = a * a
        n //= 2
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

print(f"def my_N : ℕ := 2 * 100943 * 3^39101 - 1")
print(f"def inv2_u : ℕ := {inv2.u}")
print(f"def inv2_v : ℕ := {inv2.v}")
print(f"def inv3_u : ℕ := {inv3.u}")
print(f"def inv3_v : ℕ := {inv3.v}")
print(f"def invp_u : ℕ := {invp.u}")
print(f"def invp_v : ℕ := {invp.v}")

