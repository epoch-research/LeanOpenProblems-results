def test_sum_pairs(n):
    for k in range(n):
        t1 = (k**2) % n
        t2 = ((n - k)**2) % n
        print(f"n={n}, k={k} | t1+t2={t1+t2} | n-1={n-1}")

for n in [5, 6, 7]:
    test_sum_pairs(n)
    print("-" * 20)
