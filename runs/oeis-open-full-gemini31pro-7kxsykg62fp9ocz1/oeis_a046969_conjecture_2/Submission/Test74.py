from sage.all import is_prime, divisors
n = 4789
q_D = [d+1 for d in divisors(2*n) if d+1 > 3 and is_prime(d+1)]
print(q_D)
