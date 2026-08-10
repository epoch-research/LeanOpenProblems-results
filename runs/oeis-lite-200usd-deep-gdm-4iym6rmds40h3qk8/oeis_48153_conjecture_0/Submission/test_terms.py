def test_terms(n):
    for k in range(n):
        t1 = k**2 // n
        t2 = (n - 1 - k)**2 // n
        val = 3 * t1 + 3 * t2
        diff = 2*k - 2  # let's see
        # print(f"n={n}, k={k} | val={val} | diff_term={2*n - 2*k}")
        print(f"n={n}, k={k} | val={val}")

for n in [5, 6, 7]:
    test_terms(n)
    print("-" * 20)
