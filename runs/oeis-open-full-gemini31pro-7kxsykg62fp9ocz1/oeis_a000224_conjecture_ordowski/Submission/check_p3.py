for p in range(3, 1000, 2):
    A = (p**3 - p**2 + p + 1) // 2
    M = A * (A - 1)
    if (p**6 - 1) % M == 0:
        print(f"Solution: {p}")
print("Done p^3")
