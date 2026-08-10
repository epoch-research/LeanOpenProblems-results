import math

limit = 200005 # Let's test up to 200,000 first
phi = list(range(limit))
for i in range(2, limit):
    if phi[i] == i:
        for j in range(i, limit, i):
            phi[j] -= phi[j] // i

def is_square(x):
    r = int(math.isqrt(x))
    return r * r == x

# Find all d up to 1000 that have at least one partition a+b = d
# with phi(a)*phi(b) being a square
partitions = {}
for d in range(2, 2000):
    for a in range(1, (d - 1) // 2 + 1):
        b = d - a
        if is_square(phi[a] * phi[b]):
            if d not in partitions:
                partitions[d] = []
            partitions[d].append((a, b))

print(f"Found partitions for {len(partitions)} divisors d < 2000.")

# Check even numbers
uncovered = []
for n in range(10, limit, 2):
    if n % 3 == 0 or n % 10 == 0:
        continue
    
    # We want to find a divisor d of n that has a partition (a, b)
    # such that gcd(a, n/d) == 1 and gcd(b, n/d) == 1
    found = False
    for d in range(2, min(n, 2000)):
        if n % d == 0:
            if d in partitions:
                for a, b in partitions[d]:
                    if math.gcd(a, n // d) == 1 and math.gcd(b, n // d) == 1:
                        found = True
                        break
            if found:
                break
    if not found:
        uncovered.append(n)

print(f"Total even numbers checked: {len(range(10, limit, 2))}")
print(f"Uncovered even numbers: {len(uncovered)}")
if len(uncovered) > 0:
    print(f"First 100 uncovered: {uncovered[:100]}")
