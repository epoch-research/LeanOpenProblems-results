import heapq
import math
import sympy

missing_dict = {
    1680: {1, 23, 73, 1679},
    2226: {1, 5, 25, 89, 445, 2225},
    3432: {1, 47, 73, 3431},
    3570: {1, 43, 83, 3569},
    3744: {1, 19, 197, 3743},
    4488: {1, 7, 641, 4487}
}

primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]

found = {}

def check_g(g):
    s = sympy.divisor_sigma(g)
    gc = math.gcd(s, g)
    val = (s - g) // gc
    b = g // gc
    a = s // gc
    for n, divs in missing_dict.items():
        if n in found:
            continue
        if val in divs:
            k = (n - 1) // val
            p = k * b - 1
            if p > 1 and g % p != 0 and sympy.isprime(p) and math.gcd(k * a, p) == 1:
                found[n] = (g, p, g * p)
                print(f"FOUND for {n}: g = {g}, p = {p}, i = {g * p}")

# Use a min-heap to generate smooth numbers in increasing order
heap = [(1, 0)]
limit = 10**11 # Start with a reasonable limit

print("Starting BFS smooth search...")
count = 0
while heap:
    g, last_idx = heapq.heappop(heap)
    count += 1
    if count % 200000 == 0:
        print(f"Processed {count} smooth numbers, current g = {g}")
    
    check_g(g)
    
    for i in range(last_idx, len(primes)):
        p = primes[i]
        nxt = g * p
        if nxt <= limit:
            heapq.heappush(heap, (nxt, i))

print("Finished. Found:", found)
