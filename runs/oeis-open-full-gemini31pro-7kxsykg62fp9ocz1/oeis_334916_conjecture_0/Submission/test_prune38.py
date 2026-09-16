def search(b, L):
    count = 0
    sols = []
    def dfs(k, Ak, Vk, d_prev):
        nonlocal count
        count += 1
        if k == L:
            if Ak == Vk * d_prev:
                sols.append(Ak)
            return

        m = L - k
        v = Vk * d_prev + (b - 1)
        for _ in range(m - 1):
            v = v * (b - 1) + (b - 1)
        v_max = v * (b - 1)
        
        a_min = Ak * (b ** m)
        if v_max < a_min:
            return
            
        for d in range(b):
            if k == 0 and d == 0:
                continue
            dfs(k + 1, Ak * b + d, Vk * d_prev + d if k > 0 else d, d)

    dfs(0, 0, 0, 0)
    return count, sols

import sys
# just check up to L=10
b = 38
total_nodes = 0
for L in range(1, 10):
    c, sols = search(b, L)
    total_nodes += c
    print(f"L={L}, nodes={c}, sols={sols}")
print(f"Total nodes: {total_nodes}")
