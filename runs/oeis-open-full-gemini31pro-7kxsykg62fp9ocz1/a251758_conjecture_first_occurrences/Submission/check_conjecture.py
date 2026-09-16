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

first = {}
for n in range(2, 6678672):
    a = get_a(n)
    if a not in first:
        first[a] = n
        print(f"k={a} -> {n}")
