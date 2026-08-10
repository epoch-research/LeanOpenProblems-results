import math

def solve():
    a = [0] * 3800
    a[0] = 0
    a[1] = 1
    a[2] = 1
    for n in range(3, 3800):
        g = math.gcd(a[n-1], a[n-2])
        a[n] = g + (a[n-1] + a[n-2]) // g
        
    for n in range(3775, 3790):
        formula1 = a[n] == 1 + a[n-1] + a[n-2]
        formula2 = a[n] == 2 * a[n-1] - a[n-3]
        print(f"n = {n}:")
        print(f"  A355898 n = 1 + A355898(n-1) + A355898(n-2) : {formula1}")
        print(f"  A355898 n = 2 * A355898(n-1) - A355898(n-3) : {formula2}")
        print(f"  gcd(A355898(n-1), A355898(n-2)) = {math.gcd(a[n-1], a[n-2])}")

solve()
