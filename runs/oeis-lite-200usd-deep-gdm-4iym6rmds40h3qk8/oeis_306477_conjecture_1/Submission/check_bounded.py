def choose(n, k):
    if n < k: return 0
    if k == 0 or k == n: return 1
    if k > n - k: k = n - k
    ans = 1
    for i in range(1, k + 1):
        ans = ans * (n - i + 1) // i
    return ans

# Precompute S
S = set()
for x in range(21):
    for y in range(21):
        for z in range(21):
            S.add(choose(x + 3, 4) + choose(y + 5, 6) + choose(z + 7, 8))

S = sorted(list(S))
print(f"Size of S: {len(S)}")
print(f"Max value of S: {max(S)}")

max_n = 1000000
import math

# For each n, we want to find if there is some s in S such that n - s is a triangular number
# A number t is triangular if 8t + 1 is a perfect square.
# t = w(w+1)/2 => 2t = w^2 + w => 8t + 1 = 4w^2 + 4w + 1 = (2w+1)^2.

def is_triangular(t):
    if t < 0: return False
    if t == 0: return True # w = -1, which is not nonnegative, but wait!
    # w = 0 => t = 1. w = 1 => t = 3.
    # So t must be of the form (w+1)(w+2)/2 for w >= 0.
    # So 8t + 1 = (2w+3)^2 for w >= 0.
    # So 2w+3 >= 3, meaning the square root must be an odd integer >= 3.
    val = 8 * t + 1
    r = int(math.isqrt(val))
    if r * r == val and r % 2 == 1 and r >= 3:
        return True
    return False

failed = []
for n in range(1, max_n + 1):
    found = False
    for s in S:
        if s > n: break
        if is_triangular(n - s):
            found = True
            break
    if not found:
        failed.append(n)
        if len(failed) < 10:
            print(f"Failed for n = {n}")

print(f"Total failed up to {max_n}: {len(failed)}")
