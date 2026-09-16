from test_bound import A

for n in range(3, 30, 2):
    a = A(n)
    print(f"n={n}, A={a}, M={a*(a-1)}, n^2-1={n*n-1}, M divides? {(n*n-1)%(a*(a-1)) == 0}")
