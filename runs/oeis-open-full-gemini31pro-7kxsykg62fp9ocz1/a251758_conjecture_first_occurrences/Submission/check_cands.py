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
    if n % 2 == 0: return 2
    if n % 3 == 0: return 3
    if n % 5 == 0: return 5
    if n % 7 == 0: return 7
    if n % 11 == 0: return 11
    if n % 13 == 0: return 13
    for i in range(17, int(math.isqrt(n)) + 1, 2):
        if n % i == 0: return i
    return n

count = 0
cands = []
for n in range(17, 6678671, 2):
    if n % 3 == 0 or n % 5 == 0 or n % 7 == 0 or n % 11 == 0 or n % 13 == 0:
        continue
    f = min_fac(n)
    if f >= 17 and f < n: # composite
        count += 1
        if count % 10000 == 0:
            print(f"Processed {count} composites...")
        a = get_a(n)
        if a <= 15:
            cands.append((n, a))

print("Total composites:", count)
print("Candidates with a(n) <= 15:", cands)
