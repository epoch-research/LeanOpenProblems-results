import math

def totient(n):
    t = n
    p = 2
    temp = n
    while p * p <= temp:
        if temp % p == 0:
            while temp % p == 0:
                temp //= p
            t -= t // p
        if p == 2:
            p = 3
        else:
            p += 2
    if temp > 1:
        t -= t // temp
    return t

def is_square(x):
    r = int(math.isqrt(x))
    return r * r == x

def is_uncovered(n):
    if n % 6 == 3:
        return False
    if n % 10 == 0:
        return False
    if n % 6 == 0:
        return False
    return True

# Analyze first 50,000 uncovered numbers
uncovered_witnesses = []
for n in range(9, 50000 + 1):
    if is_uncovered(n):
        for k in range(1, (n - 1) // 2 + 1):
            val = totient(k) * totient(n - k)
            if is_square(val):
                uncovered_witnesses.append(k)
                break

from collections import Counter
counts = Counter(uncovered_witnesses)
print("Distribution of witness k:")
for k in sorted(counts.keys())[:15]:
    print(f"k = {k}: {counts[k]} ({counts[k]/len(uncovered_witnesses)*100:.2f}%)")

print(f"Total analyzed: {len(uncovered_witnesses)}")
print(f"Max k in sample: {max(uncovered_witnesses)}")
print(f"Average k in sample: {sum(uncovered_witnesses)/len(uncovered_witnesses):.2f}")
