from test_bound import A
import math

for n in range(3, 100000, 2):
    is_prime = True
    for i in range(2, int(n**0.5)+1):
        if n % i == 0:
            is_prime = False
            break
    if is_prime: continue
    
    a = A(n)
    M = a * (a - 1)
    if math.gcd(M, n) == 1:
        print(f"M is coprime to n for n={n}, A(n)={a}")
