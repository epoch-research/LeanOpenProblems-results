import math

# We'll use a fast check
def is_uncovered(n):
    if n % 6 == 3:
        return False
    if n % 10 == 0:
        return False
    if n % 6 == 0:
        return False
    
    # rule_coprime c
    for c in [10, 12, 34, 40, 48, 60, 85]:
        if n % (c + 1) == 0:
            if math.gcd(c, n // (c + 1)) == 1:
                return False
    return True

count = 0
for n in range(9, 2000000 + 1):
    if is_uncovered(n):
        count += 1

print(f"Total uncovered in [9, 2,000,000]: {count}")
