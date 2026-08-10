import math

def is_prime(n):
    if n < 2: return False
    for i in range(2, int(math.sqrt(n))+1):
        if n % i == 0: return False
    return True

def min_prime_factor(n):
    for i in range(2, int(math.sqrt(n))+1):
        if n % i == 0: return i
    return n

def solve():
    count = 0
    for p in range(2, 1000000):
        if is_prime(p):
            if not is_prime(p-2):
                r = min_prime_factor(p-2)
                if r > 47:
                    print(f"p = {p}, p-2 = {p-2}, min_prime_factor = {r}")
                    count += 1
                    if count >= 10:
                        break

if __name__ == '__main__':
    solve()
