def sum_digits(m):
    return sum(int(c) for c in str(m))

for k in range(1, 100):
    if sum_digits(k * 55) == k:
        print(f"For n=55, valid k={k}, k*n={k*55}")
