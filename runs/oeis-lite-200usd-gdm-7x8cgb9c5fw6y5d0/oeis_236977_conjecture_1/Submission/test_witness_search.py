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

def has_algebraic_rule(n):
    if n % 6 == 3:
        return True
    if n % 10 == 0:
        return True
    if n % 6 == 0:
        return True
    return False

max_k = 0
total_k_searched = 0
uncovered_count = 0

for n in range(9, 100000 + 1):
    if not has_algebraic_rule(n):
        uncovered_count += 1
        # Search for witness k
        found = False
        for k in range(1, (n - 1) // 2 + 1):
            val = totient(k) * totient(n - k)
            if is_square(val):
                found = True
                max_k = max(max_k, k)
                total_k_searched += k
                break
        if not found:
            print(f"FAILED TO FIND WITNESS FOR n={n}!")
            exit(1)

print(f"Processed {uncovered_count} uncovered numbers.")
print(f"Max k needed: {max_k}")
print(f"Average k searched: {total_k_searched / uncovered_count:.2f}")
