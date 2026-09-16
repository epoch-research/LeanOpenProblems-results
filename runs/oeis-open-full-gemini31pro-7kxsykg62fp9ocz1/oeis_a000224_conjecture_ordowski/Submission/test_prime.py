for n in range(3, 1000, 2):
    is_prime = True
    for i in range(2, int(n**0.5)+1):
        if n % i == 0:
            is_prime = False
            break
    if not is_prime: continue
    
    a = (n+1)//2
    M = a * (a - 1)
    if (n*n - 1) % M != 0:
        print(f"Prime counterexample: {n}")
