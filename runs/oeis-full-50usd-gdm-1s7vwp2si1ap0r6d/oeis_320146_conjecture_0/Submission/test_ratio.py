def is_prime(n):
    if n < 2: return False
    for i in range(2, int(n**0.5) + 1):
        if n % i == 0: return False
    return True

primes = []
num = 2
while len(primes) < 100000:
    if is_prime(num):
        primes.append(num)
    num += 1

def P(i):
    return primes[i]

def A320146(n):
    return (2 * P(n - 1)) % (P(n - 2) + P(n))

def prime_oeis(n):
    return P(n - 1)

# Let's compute the ratios for n from 2 to 100000
sum_A = 0
sum_P = 0
ratios = []
for n in range(2, 100000):
    sum_A += A320146(n)
    sum_P += prime_oeis(n)
    if n % 10000 == 0 or n < 10:
        ratio = sum_A / sum_P
        print(f"n={n}: {ratio}")

