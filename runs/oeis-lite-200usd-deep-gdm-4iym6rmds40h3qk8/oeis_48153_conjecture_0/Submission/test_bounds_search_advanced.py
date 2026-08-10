def search_bounds():
    # We want 3 * (k^2 // n) + A * n + B >= 2 * D * k for all 5 <= n <= 15 and all k < n.
    # And we want the sum of this bound:
    # Sum_{k=0}^{n-1} (2*D*k - A*n - B) = D*n*(n-1) - A*n^2 - B*n >= (n-1)*(n-2).
    
    for D in range(1, 10):
        for A in range(-15, 15):
            for B in range(-15, 15):
                ok_sum = True
                for n in range(5, 30):
                    val = D * n * (n-1) - A * n * n - B * n
                    target = (n-1)*(n-2)
                    if val < target:
                        ok_sum = False
                        break
                if not ok_sum:
                    continue
                
                ok_term = True
                for n in range(5, 30):
                    for k in range(n):
                        lhs = 3 * (k**2 // n) + A * n + B
                        rhs = 2 * D * k
                        if lhs < rhs:
                            ok_term = False
                            break
                    if not ok_term:
                        break
                
                if ok_term:
                    print(f"FOUND: D={D}, A={A}, B={B}")
                    for n in range(5, 10):
                        val = D * n * (n-1) - A * n * n - B * n
                        target = (n-1)*(n-2)
                        print(f"  n={n}: sum={val}, target={target}")

search_bounds()
