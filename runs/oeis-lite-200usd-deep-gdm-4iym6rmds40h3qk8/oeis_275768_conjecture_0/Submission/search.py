def is_prime(n):
    if n < 2: return False
    for i in range(2, int(n**0.5)+1):
        if n % i == 0: return False
    return True

def a(n):
    count = 0
    for q in range(n):
        if is_prime(q) and is_prime(n - q) and is_prime(n + q):
            count += 1
    return count

for n in range(24, 1000, 6):
    val = a(n)
    print(f"a({n}) = {val}")
    if val == 4:
        print(f"FOUND COUNTEREXAMPLE: a({n}) = 4")
        break
