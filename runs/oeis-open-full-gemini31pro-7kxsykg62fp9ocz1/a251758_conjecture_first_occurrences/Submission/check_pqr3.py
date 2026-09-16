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

primes = [p for p in range(17, 300) if all(p % d != 0 for d in range(2, int(math.isqrt(p))+1))]
count = 0
for i in range(len(primes)):
    for j in range(i, len(primes)):
        for k in range(j, len(primes)):
            for m in range(k, len(primes)):
                n = primes[i] * primes[j] * primes[k] * primes[m]
                if n < 6678671:
                    a = get_a(n)
                    if a <= 14:
                        print(f"p={primes[i]}, q={primes[j]}, r={primes[k]}, m={primes[m]}, a={a}")
                        count += 1
print("Done 4, count=", count)
