import math
import sys

def search(limit):
    sieve = [True] * (int(math.sqrt(limit)) + 5)
    sieve[0] = sieve[1] = False
    for i in range(2, int(math.sqrt(len(sieve))) + 1):
        if sieve[i]:
            for j in range(i*i, len(sieve), i):
                sieve[j] = False
    primes = set([i for i, b in enumerate(sieve) if b])
    
    gp = []
    z = 0
    while True:
        p1 = z * (3 * z + 1) // 2
        p2 = (-z) * (3 * (-z) + 1) // 2
        added = False
        if z == 0:
            if p1 <= limit: gp.append(p1); added = True
        else:
            if p2 <= limit: gp.append(p2); added = True
            if p1 <= limit: gp.append(p1); added = True
        if not added:
            break
        z += 1
    
    a = [0] * (limit + 1)
    
    for x in range(int(math.sqrt(limit)) + 1):
        x2 = x * x
        for y in range(x, int(math.sqrt(limit - x2)) + 1):
            if (x + 1) in primes or (y + 1) in primes:
                s = x2 + y * y
                for p in gp:
                    n = s + p
                    if n <= limit:
                        a[n] += 1
    
    for n in range(1, limit + 1):
        if a[n] == 0:
            print(f"Counterexample to a(n) > 0: n = {n}")
        if a[n] == 1 and n not in [1, 49, 608]:
            print(f"Counterexample to a(n) = 1: n = {n}")

search(500000)
