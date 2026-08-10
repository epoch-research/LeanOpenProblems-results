def search():
    # We want 3 * (k^2 // n) >= D * k - A * n - B
    # so that Sum_{k=0}^{n-1} (D * k - A * n - B) >= (n-1)*(n-2).
    # Sum is D * n * (n-1) / 2 - A * n^2 - B * n.
    # To avoid division by 2, let's say:
    # 6 * (k^2 // n) >= 2 * D * k - 2 * A * n - 2 * B
    # Sum is D * n * (n-1) - 2 * A * n^2 - 2 * B * n.
    # We want this sum to be >= 2 * (n-1) * (n-2) = 2 * n^2 - 6 * n + 4.
    
    # Let's search for D, A, B such that:
    # 3 * (k^2 // n) + A * n + B >= D * k
    # holds for all n >= 5, k < n.
    # And we want the sum of (D * k - A * n - B) over k=0..n-1 to be >= (n-1)*(n-2).
    # Sum = D * n * (n-1) / 2 - A * n^2 - B * n.
    # Let's test D, A, B.
    for D in range(1, 10):
        for A in range(-10, 10):
            for B in range(-10, 10):
                # Check term-by-term inequality:
                ok_term = True
                for n in range(5, 40):
                    for k in range(n):
                        lhs = 3 * (k**2 // n) + A * n + B
                        rhs = D * k
                        if lhs < rhs:
                            ok_term = False
                            break
                    if not ok_term:
                        break
                if not ok_term:
                    continue
                
                # Check sum condition:
                ok_sum = True
                for n in range(5, 40):
                    # We can compute the sum exactly (using float division since we want to compare)
                    sum_val = D * n * (n - 1) / 2 - A * n * n - B * n
                    target = (n - 1) * (n - 2)
                    if sum_val < target - 1e-9:
                        ok_sum = False
                        break
                if ok_sum:
                    print(f"FOUND: D={D}, A={A}, B={B}")
                    return

search()
