import sympy
from sympy import binomial

def a108625_aux(n, k):
    ans = 0
    for i in range(k + 1):
        ans += binomial(n, i)**2 * binomial(n + k - i, k - i)
    return ans

def A376462(n):
    ans = 0
    for k in range(n + 1):
        ans += binomial(n, k)**2 * binomial(n + k, k) * a108625_aux(n, n - k)
    return ans

# Let's test the conjecture for p=5, n=1, r=1
# A(5) mod 5^3 vs A(1) mod 5^3
p = 5
n = 1
r = 1
val_1_lhs = A376462(n * p**r)
val_1_rhs = A376462(n * p**(r - 1))
modulus = p**(3 * r)
print(f"A(5) = {val_1_lhs}")
print(f"A(1) = {val_1_rhs}")
print(f"A(5) = {val_1_lhs % modulus} (mod {modulus})")
print(f"A(1) = {val_1_rhs % modulus} (mod {modulus})")
print(f"Congruence 1 holds: {val_1_lhs % modulus == val_1_rhs % modulus}")

val_2_lhs = A376462(n * p**r - 1)
val_2_rhs = A376462(n * p**(r - 1) - 1)
print(f"A(4) = {val_2_lhs}")
print(f"A(0) = {val_2_rhs}")
print(f"A(4) = {val_2_lhs % modulus} (mod {modulus})")
print(f"A(0) = {val_2_rhs % modulus} (mod {modulus})")
print(f"Congruence 2 holds: {val_2_lhs % modulus == val_2_rhs % modulus}")
