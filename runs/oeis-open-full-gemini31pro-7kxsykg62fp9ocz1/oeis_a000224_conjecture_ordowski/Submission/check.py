def A(n):
    return len(set(x**2 % n for x in range(n)))

for n in range(2, 1000):
    a = A(n)
    if (n**2 - 1) % (a * (a - 1)) == 0:
        print(f"Match: {n}, prime? {n in [2,3,5,7,11,13,17,19,23,29,31,37,41]}")
