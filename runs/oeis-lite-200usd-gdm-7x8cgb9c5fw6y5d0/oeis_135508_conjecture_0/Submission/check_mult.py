import math

def solve():
    x = [0] * 100
    x[0] = 0
    x[1] = 1
    multipliers = [0] * 100
    for i in range(2, 100):
        g = math.gcd(x[i-1], i)
        m = 2 + i // g
        multipliers[i] = m
        x[i] = x[i-1] * m
        print(f"i = {i:2d}: multiplier = {m:2d}, x_seq = {x[i]}, prime factors of multiplier: {[f for f in range(2, m+1) if m % f == 0 and all(f % j != 0 for j in range(2, f))]}")

if __name__ == '__main__':
    solve()
