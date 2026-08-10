# Search for coefficients
for n in range(5, 10):
    residues = [(k**2) % n for k in range(n)]
    sum_res = sum(residues)
    target = n * (n - 1) // 2
    print(f"n={n} | sum_res={sum_res} | target={target}")
