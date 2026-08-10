def precompute_V():
    V = {1}
    for s in range(40):
        fs = (10 * 16**s + 16 * 4**s + 10) // 9
        for i in range(160):
            val = fs * 4**i
            V.add(val)
    return sorted(list(V))

V_all = precompute_V()
V_10_12 = [v for v in V_all if v < 10**12]
print(f"Number of v < 10^12: {len(V_10_12)}")
