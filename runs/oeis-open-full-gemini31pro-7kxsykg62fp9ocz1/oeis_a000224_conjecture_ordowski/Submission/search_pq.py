import math

def check():
    # p+1 | 16(q^2-1) and q+1 | 16(p^2-1)
    # Actually, we can just search p and q.
    for p in range(3, 100000, 2):
        if not is_prime(p): continue
        for q in range(p, 100000, 2):
            if not is_prime(q): continue
            A = (p + 1) * (q + 1) // 4
            M = A * (A - 1)
            if M == 0: continue
            if (p*q*p*q - 1) % M == 0:
                print(f"Found! p={p}, q={q}, n={p*q}")

def is_prime(n):
    if n < 2: return False
    if n in (2,3): return True
    if n % 2 == 0 or n % 3 == 0: return False
    for i in range(5, int(n**0.5)+1, 6):
        if n % i == 0 or n % (i+2) == 0: return False
    return True

check()
