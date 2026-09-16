def sum_digits(m):
    return sum(int(c) for c in str(m))

for k in [1, 2, 3, 4, 5, 6, 7, 8, 10, 11]:
    for n in range(1, 100000):
        if sum_digits(k * n) == k:
            print(f"Found k={k}, n={n}, k*n={k*n}")
