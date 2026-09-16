import math

def get_primes(limit):
    sieve = [True] * (limit + 1)
    sieve[0] = sieve[1] = False
    for i in range(2, int(math.sqrt(limit)) + 1):
        if sieve[i]:
            for j in range(i*i, limit + 1, i):
                sieve[j] = False
    return [i for i, b in enumerate(sieve) if b]

def search(limit):
    primes = set(get_primes(int(math.sqrt(limit)) + 5))
    
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
    
    max_x = int(math.sqrt(limit)) + 1
    for x in range(max_x):
        x2 = x * x
        if x2 > limit: break
        max_y = int(math.sqrt(limit - x2)) + 1
        for y in range(x, max_y):
            s = x2 + y * y
            if s > limit: break
            if (x + 1) in primes or (y + 1) in primes:
                for p in gp:
                    n = s + p
                    if n <= limit:
                        a[n] += 1
    
    for n in range(1, limit + 1):
        if a[n] == 0:
            print(f"Counterexample to a(n) > 0: n = {n}")
        if a[n] == 1 and n not in [1, 49, 608]:
            print(f"Counterexample to a(n) = 1: n = {n}")

search(1000000)
