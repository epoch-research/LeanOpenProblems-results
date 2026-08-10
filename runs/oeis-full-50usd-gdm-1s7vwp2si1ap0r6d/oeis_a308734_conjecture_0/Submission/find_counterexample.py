import math

def is_sum_of_two_squares(n):
    if n < 0:
        return False
    # A number is a sum of two squares iff every prime factor p = 3 (mod 4) appears with an even exponent.
    # But since n is small, we can also just check directly or use factorization.
    # Direct check is fast enough for individual numbers.
    # Alternatively, factorize using trial division:
    temp = n
    # check factor of 2
    while temp % 2 == 0:
        temp //= 2
    d = 3
    while d * d <= temp:
        if temp % d == 0:
            count = 0
            while temp % d == 0:
                count += 1
                temp //= d
            if d % 4 == 3 and count % 2 != 0:
                return False
        d += 2
    if temp > 1 and temp % 4 == 3:
        return False
    return True

def has_solution(n):
    # We want to find a, b, c, d such that n - (2^a * 3^b)^2 - (2^c * 5^d)^2 is a sum of two squares.
    # Let S1 = 2^a * 3^b, S2 = 2^c * 5^d.
    # term1 = S1^2, term2 = S2^2.
    # term1 + term2 <= n.
    # Since we need to find AT LEAST one solution, we can iterate over a, b such that term1 <= n.
    # And c, d such that term1 + term2 <= n.
    limit = int(math.isqrt(n))
    # We can precompute all possible values of S1^2 and S2^2 <= n.
    S1_sq = []
    a = 0
    while True:
        p2 = 2**a
        if p2**2 > n:
            break
        b = 0
        while True:
            val = p2 * (3**b)
            if val**2 > n:
                break
            S1_sq.append(val**2)
            b += 1
        a += 1
    
    S2_sq = []
    c = 0
    while True:
        p2 = 2**c
        if p2**2 > n:
            break
        d = 0
        while True:
            val = p2 * (5**d)
            if val**2 > n:
                break
            S2_sq.append(val**2)
            d += 1
        c += 1

    for t1 in S1_sq:
        for t2 in S2_sq:
            rem = n - t1 - t2
            if rem >= 0 and is_sum_of_two_squares(rem):
                return True
    return False

# Let's test for n > 1.
print("Starting search...")
for n in range(2, 200000):
    if not has_solution(n):
        print(f"Counterexample found: n = {n}")
        break
else:
    print("No counterexample found up to 200,000")
