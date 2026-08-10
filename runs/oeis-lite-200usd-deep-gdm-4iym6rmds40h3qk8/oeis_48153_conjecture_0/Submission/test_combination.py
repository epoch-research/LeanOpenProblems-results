def A(n):
    return sum((k**2) % n for k in range(n))

for n in range(5, 12):
    val = A(n)
    target = n * (n - 1) // 2
    
    # For each k, we can choose one of the bounds:
    # 0: k^2
    # 1: (n-k)^2
    # 2: k * (n-1) // 2
    # 3: (n-k) * (n-1) // 2
    # 4: n - 1
    # 5: k * (n-k)
    
    # We want to find a choice for each k that minimizes the sum of bounds,
    # while ensuring that the chosen bound is indeed a valid upper bound for k^2 % n.
    # Actually, all 0..5 are valid upper bounds for k^2 % n (for n >= 5).
    # So we can just take the minimum of all of them for each k!
    # But wait, we already did that in test_all_min.py and it was too large for n >= 9.
    # Is there ANY other valid upper bound?
    # What about:
    # k^2 % n <= k? (False)
    # k^2 % n <= n - k? (False)
    
    print(f"n={n}")
