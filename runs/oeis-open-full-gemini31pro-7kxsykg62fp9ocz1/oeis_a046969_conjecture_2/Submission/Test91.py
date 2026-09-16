from sage.all import divisors, is_prime
n = 49177

def check_div(n):
    m = 2*n
    q_D = [d+1 for d in divisors(m) if d+1 > 3 and is_prime(d+1)]
    return q_D

print("n-1 =", n-1)
print(check_div(n-1))
print("n+2 =", n+2)
print(check_div(n+2))
