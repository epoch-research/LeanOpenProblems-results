def choose(n, k):
    if n < k: return 0
    if k == 0 or k == n: return 1
    if k > n - k: k = n - k
    ans = 1
    for i in range(1, k + 1):
        ans = ans * (n - i + 1) // i
    return ans

def greedy_check(max_n):
    failed = []
    for n in range(1, max_n + 1):
        # greedy search
        # find largest z
        rem = n
        z = 0
        while choose(z + 8, 8) <= rem:
            z += 1
        z -= 1
        if z < 0: z = 0
        rem -= choose(z + 7, 8)

        y = 0
        while choose(y + 6, 6) <= rem:
            y += 1
        y -= 1
        if y < 0: y = 0
        rem -= choose(y + 5, 6)

        x = 0
        while choose(x + 4, 4) <= rem:
            x += 1
        x -= 1
        if x < 0: x = 0
        rem -= choose(x + 3, 4)

        w = 0
        while choose(w + 2, 2) <= rem:
            w += 1
        w -= 1
        if w < 0: w = 0
        rem -= choose(w + 2, 2)

        if rem != 0:
            failed.append(n)
    print(f"Greedy failed for {len(failed)} numbers up to {max_n}")
    if failed:
        print(f"First few failed: {failed[:10]}")

greedy_check(1000)
