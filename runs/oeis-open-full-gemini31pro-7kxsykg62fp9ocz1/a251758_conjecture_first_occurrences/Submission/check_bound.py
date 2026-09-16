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

def min_fac(n):
    for i in range(2, int(math.isqrt(n)) + 1):
        if n % i == 0: return i
    return n

count = 0
for n in range(2, 500000):
    if get_a(n) > min_fac(n):
        print(f"Counterexample! n={n}, a={get_a(n)}, minFac={min_fac(n)}")
        count += 1
print("Done, found", count)
