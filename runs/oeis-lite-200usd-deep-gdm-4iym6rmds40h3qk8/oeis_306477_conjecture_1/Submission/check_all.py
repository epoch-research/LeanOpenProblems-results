def choose(n, k):
    if n < k: return 0
    if k == 0 or k == n: return 1
    if k > n - k: k = n - k
    ans = 1
    for i in range(1, k + 1):
        ans = ans * (n - i + 1) // i
    return ans

for n in range(1, 101):
    found = False
    for w in range(n + 1):
        for x in range(n + 1):
            for y in range(n + 1):
                for z in range(n + 1):
                    val = choose(w + 2, 2) + choose(x + 3, 4) + choose(y + 5, 6) + choose(z + 7, 8)
                    if val == n:
                        print(f"n = {n}: w={w}, x={x}, y={y}, z={z}")
                        found = True
                        break
                if found: break
            if found: break
        if found: break
