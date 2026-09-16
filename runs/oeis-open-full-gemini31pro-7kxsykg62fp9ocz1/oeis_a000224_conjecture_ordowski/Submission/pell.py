for n in range(2, 10000):
    # check if n is composite
    is_prime = True
    for i in range(2, int(n**0.5)+1):
        if n % i == 0:
            is_prime = False
            break
    if is_prime: continue
    
    n2 = n*n - 1
    for x in range(2, n):
        M = x*(x-1)
        if n2 % M == 0:
            print(f"Composite n={n}, x={x}, k={n2//M}")
