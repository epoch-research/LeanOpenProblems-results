for p in range(3, 1000, 2):
    M = (p**4 - 2*p**3 + 3*p**2 - 2*p) // 4
    if (p**4 - 1) % M == 0:
        print(f"Solution: {p}")
print("Done p^2")
