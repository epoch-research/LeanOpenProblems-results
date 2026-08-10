import math

def is_prime(n):
    if n < 2: return False
    for i in range(2, int(math.isqrt(n)) + 1):
        if n % i == 0: return False
    return True

# Generate primes up to 2 * 10^6
primes = []
for i in range(2, 2000000):
    if is_prime(i):
        primes.append(i)

prime_set = set(primes)

print("Primes generated.")

for n in range(3, 1000000):
    found = False
    for p in primes:
        if p >= n:
            break
        val = math.isqrt(n + p)
        if val in prime_set:
            found = True
            break
    if not found:
        print(f"Counterexample found: {n}")
        break
else:
    print("No counterexamples found up to 1,000,000.")
