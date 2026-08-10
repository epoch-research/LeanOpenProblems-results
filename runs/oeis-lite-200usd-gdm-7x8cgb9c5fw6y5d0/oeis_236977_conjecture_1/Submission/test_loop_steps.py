import math

# Primes up to 1414
limit = 1414
is_prime = [True] * (limit + 1)
is_prime[0] = is_prime[1] = False
for i in range(2, int(math.isqrt(limit)) + 1):
    if is_prime[i]:
        for j in range(i*i, limit + 1, i):
            is_prime[j] = False
primes_1414 = [p for p in range(limit + 1) if is_prime[p]]

def count_steps(n):
    if n <= 1:
        return 0
    steps = 0
    temp = n
    for p in primes_1414:
        steps += 1
        if p * p > temp:
            break
        if temp % p == 0:
            while temp % p == 0:
                temp //= p
    return steps

def is_uncovered(n):
    if n % 6 == 3:
        return False
    if n % 10 == 0:
        return False
    if n % 6 == 0:
        return False
    return True

total_steps = 0
count = 0
for n in range(9, 2000000 + 1):
    if is_uncovered(n):
        count += 1
        # L - k is what we evaluate.
        # Since k is small, L - k is very close to L.
        # So we can just measure count_steps(n)
        total_steps += count_steps(n)

print(f"Total uncovered: {count}")
print(f"Total loop steps: {total_steps}")
print(f"Average loop steps per uncovered number: {total_steps / count:.2f}")
