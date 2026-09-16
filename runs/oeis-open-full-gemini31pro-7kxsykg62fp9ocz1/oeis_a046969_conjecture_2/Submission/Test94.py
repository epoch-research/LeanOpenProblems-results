from sage.all import is_prime, factor, divisors
n = 1269
m = 2*n
print(f"n = {n}, m = {m}")
print("m-1 =", m-1)
print("factor(m-1) =", factor(m-1))
q_D = [d+1 for d in divisors(m) if d+1 > 3 and is_prime(d+1)]
print("q_D =", q_D)
