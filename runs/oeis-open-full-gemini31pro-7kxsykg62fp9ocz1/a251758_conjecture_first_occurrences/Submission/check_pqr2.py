import math
def get_a(n):
    divs = []
    for i in range(1, int(math.isqrt(n)) + 1):
        if n % i == 0:
            divs.append(i)
            if i * i != n:
                divs.append(n // i)
    divs.sort()
    s = 0
    for i in range(len(divs) - 1):
        s += divs[i] * divs[i+1]
    if s == 0: return 0
    return (n * n) // s

primes = [p for p in range(17, 1000) if all(p % d != 0 for d in range(2, int(math.isqrt(p))+1))]
count = 0
for p in primes:
    for q in primes:
        if q >= p:
            for r in primes:
                if r >= q:
                    n = p * q * r
                    if n < 6678671:
                        a = get_a(n)
                        if a <= 14:
                            print(f"p={p}, q={q}, r={r}, a={a}")
                            count += 1
print("Done, count=", count)
