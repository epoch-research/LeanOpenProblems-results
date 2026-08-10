def search():
    for A in range(1, 5):
        for B in range(-15, 5):
            # Check if 6 * (j^2 // n) + 3*n - 6*j >= A * n + B for all n >= 13, j < n/2
            ok = True
            for n in range(13, 100):
                for j in range(1, (n - 1) // 2 + 1):
                    lhs = 6 * (j**2 // n) + 3 * n - 6 * j
                    rhs = A * n + B
                    if lhs < rhs:
                        ok = False
                        break
                if not ok:
                    break
            if ok:
                # Let's check the sum condition:
                # Sum_{j=1}^{m-1} (A * n + B) + (n - 2) >= (n-1)*(n-2) (if n is even)
                # Sum_{j=1}^m (A * n + B) >= (n-1)*(n-2) (if n is odd)
                # Let's test the sum condition for n in range 13..100
                sum_ok = True
                for n in range(13, 100):
                    m = n // 2
                    if n % 2 == 0:
                        val = (m - 1) * (A * n + B) + (n - 2)
                    else:
                        val = m * (A * n + B)
                    target = (n - 1) * (n - 2)
                    if val < target:
                        sum_ok = False
                        break
                if sum_ok:
                    print(f"FOUND: A={A}, B={B}")
                    return

search()
