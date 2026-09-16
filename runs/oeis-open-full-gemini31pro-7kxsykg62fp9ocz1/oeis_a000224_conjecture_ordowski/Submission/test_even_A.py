from test_bound import A

for n in range(3, 10000, 2):
    is_prime = True
    for i in range(2, int(n**0.5)+1):
        if n % i == 0:
            is_prime = False
            break
    if is_prime: continue
    
    a = A(n)
    if a % 2 != 0:
        print(f"Odd A(n) for composite n={n}, A(n)={a}")
