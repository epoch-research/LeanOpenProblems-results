def S(m):
    return sum(int(c) for c in str(m))
m = 23
n = (10**m - 1) // 9
valid = [k for k in range(1, 1000) if S(k*n) == k]
print(f"len 23 valid={valid}")
