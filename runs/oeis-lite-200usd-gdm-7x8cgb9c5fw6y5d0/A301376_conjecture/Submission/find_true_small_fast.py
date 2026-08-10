import math

# Fast sieve for sum of two squares up to 2 * 10^8 (i.e. N <= 10000)
LIMIT = 200000000
print("Sieving...", flush=True)
is_prime = [True] * LIMIT
is_prime[0] = is_prime[1] = False
for i in range(2, int(LIMIT**0.5) + 1):
    if is_prime[i]:
        for j in range(i*i, LIMIT, i):
            is_prime[j] = False

# A number is a sum of two squares if and only if its prime factors of form 4k+3 have even exponents
def is_sum_of_two_squares_fast(n):
    if n < 0: return False
    if n == 0 or n == 1: return True
    temp = n
    # We only need to check prime factors up to sqrt(temp)
    limit = int(temp**0.5)
    for p in range(2, limit + 1):
        if is_prime[p]:
            if temp % p == 0:
                count = 0
                while temp % p == 0:
                    count += 1
                    temp //= p
                if p % 4 == 3 and count % 2 != 0:
                    return False
            if temp == 1:
                break
    if temp > 1:
        if temp % 4 == 3:
            return False
    return True

def has_actual_solution(N):
    N2 = N * N
    max_v = int(math.log2(N)) + 2
    for v in range(max_v + 1):
        for u in range(v + 1):
            if (2**v - 2**u) % 6 == 0:
                x = (2**v + 2**u) // 2
                y = (2**v - 2**u) // 6
                val = x*x + y*y
                if val <= N2:
                    if is_sum_of_two_squares_fast(N2 - val):
                        return True
    return False

print("Searching...", flush=True)
for N in range(1, 10000):
    if N % 500 == 0:
        print(f"Checking N = {N}...", flush=True)
    if not has_actual_solution(N):
        print(f"FOUND TRUE COUNTEREXAMPLE N = {N}")
        break
