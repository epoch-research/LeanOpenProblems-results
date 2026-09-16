def S(m):
    return sum(int(c) for c in str(m))
n = int("1" + "0"*10 + "1" + "0"*10 + "1" + "0"*10 + "1" + "0"*10 + "1" + "0"*10 + "1" + "0"*10 + "1" + "0"*10 + "1" + "0"*10 + "1" + "0"*10 + "1")
print(f"S(n) = {S(n)}")
for k in range(11, 200):
    if S(k * n) == k:
        print(f"Valid k: {k}")
