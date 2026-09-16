import sympy as sp

def is_prime(n):
    if n < 2: return False
    if n in (2, 3): return True
    if n % 2 == 0 or n % 3 == 0: return False
    for i in range(5, int(n**0.5) + 1, 6):
        if n % i == 0 or n % (i+2) == 0: return False
    return True

c = {4: -3, 6: -2, 12: -1, 14: 2, 16: -2, 18: 1, 24: 2, 26: 3, 28: 1}

for i in range(1, 40):
    val = 0
    for j, coef in c.items():
        if is_prime(i**2 + j**2):
            val += coef
    print(f"i={i}, sum={val}")

