def S(m):
    return sum(int(c) for c in str(m))

def check(n):
    max_k = 0
    for k in range(11, 200):
        if S(k * n) == k:
            return k
    return 0

# We want to find a number n with S(n) = 10 that avoids all k > 10.
# Since digits must overlap to avoid the "no-carry" multipliers, n must be small!
# If n is small (e.g. < 10^8), we ALREADY checked all n < 10^8 in check_huge.cpp!
print("Done")
