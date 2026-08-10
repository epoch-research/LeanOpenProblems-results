def S_sq(n):
    return (n - 1) * n * (2 * n - 1) // 6

# We have 6 * S + n^2 >= 3 * n * (n-1) / 2 (where S = sum k^2/n)
# So S >= (3 * n * (n-1) / 2 - n^2) / 6
# Thus, S_est = ceil( (1.5 * n * (n-1) - n^2) / 6 )
# Let's check if S_sq - n * S_est <= n * (n-1) / 2.

for n in range(6, 200):
    # S_lower_bound is the floor division because S is integer
    # 12 * S + 2 * n^2 >= 3 * n * (n-1)
    # 12 * S >= 3 * n * (n-1) - 2 * n^2
    # S >= ceil( (3*n*(n-1) - 2*n^2) / 12 )
    S_est = (3 * n * (n - 1) - 2 * n * n + 11) // 12
    A_est = S_sq(n) - n * S_est
    target = n * (n - 1) // 2
    if A_est <= target:
        print(f"n={n:3d} works! A_est={A_est}, target={target}")
        exit()
print("None worked.")
