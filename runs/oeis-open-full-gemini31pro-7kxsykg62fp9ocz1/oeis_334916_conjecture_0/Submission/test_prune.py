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
        # Max V
        # If m = 1, next digit is d. Final is (Vk * d_prev + d) * d
        # Wait, if we use the bound: max over all d of (Vk * d_prev + d) * d
        # That is when d = b-1. So V_final_max = (Vk * d_prev + b - 1) * (b - 1)
        # For m > 1, first step gives (Vk * d_prev + b - 1), then m-1 steps of (b-1)
        
        # Calculate V_max_final
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

print("Base 6:")
for L in range(1, 12):
    c, sols = search(6, L)
    print(f"L={L}, nodes={c}, sols={sols}")

print("Base 10:")
for L in range(1, 40): # max L for base 10 is around 22
    if L > 22: break
    c, sols = search(10, L)
    print(f"L={L}, nodes={c}, sols={sols}")

