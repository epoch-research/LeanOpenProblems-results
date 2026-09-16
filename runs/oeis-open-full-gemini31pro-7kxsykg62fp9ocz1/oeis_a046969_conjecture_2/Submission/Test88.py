from sage.all import is_prime, divisors
m = 98354
q_D = [d+1 for d in divisors(m) if d+1 > 3 and is_prime(d+1)]
print("q_D =", q_D)
