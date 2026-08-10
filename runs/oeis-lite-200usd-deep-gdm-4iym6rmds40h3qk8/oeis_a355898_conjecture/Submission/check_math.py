def gcd(a, b):
    while b:
        a, b = b, a % b
    return a

a = [0] * 50
a[1] = 1
a[2] = 1
for n in range(3, 50):
    g = gcd(a[n-1], a[n-2])
    a[n] = g + (a[n-1] + a[n-2]) // g

for n in range(5, 45):
    print(f"n={n}: gcd(a[n], a[n-1])={gcd(a[n], a[n-1])}, gcd(1+a[n-2], a[n-3])={gcd(1+a[n-2], a[n-3])}")
