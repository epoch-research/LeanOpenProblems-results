def sum_digits(m):
    return sum(int(c) for c in str(m))

def max_valid(n):
    max_k = 0
    for k in range(1, 100):
        if sum_digits(k * n) == k:
            max_k = k
    return max_k

for n in [1, 10, 55, 100, 505]:
    print(f"n={n}, max_k >= {max_valid(n)}")
