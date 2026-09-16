from sage.all import is_prime, divisors

def possible_prime(n):
    # check if there are >= 2 primes q > 3 such that q-1 | 2n
    count = 0
    for d in divisors(2*n):
        q = d + 1
        if q > 3 and is_prime(q):
            count += 1
            if count >= 2:
                return False
    return True

matches = []
for n in range(2, 50000):
    if possible_prime(n):
        matches.append(n)
print("Possible n:", matches)
