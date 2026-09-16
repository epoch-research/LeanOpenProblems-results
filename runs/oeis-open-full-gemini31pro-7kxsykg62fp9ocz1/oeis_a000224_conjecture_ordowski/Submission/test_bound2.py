from test_bound import A

for n in range(3, 100000, 2):
    is_prime = True
    for i in range(2, int(n**0.5)+1):
        if n % i == 0:
            is_prime = False
            break
    if is_prime: continue
    
    a = A(n)
    M = a * (a - 1)
    if M >= n*n - 1:
        print(f"FAILED bound for n={n}, A(n)={a}, M={M}, n^2-1={n*n-1}")
