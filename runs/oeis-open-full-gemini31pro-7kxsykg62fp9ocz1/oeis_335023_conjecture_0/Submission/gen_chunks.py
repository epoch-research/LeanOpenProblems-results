P = 1093**1092

def dc_mod(a, b):
    if a + 1 == b:
        k = a + 1
        return (k % P, k % P if k % 2 == 0 else (P - k % P) % P)
    mid = (a + b) // 2
    x1, z1 = dc_mod(a, mid)
    x2, z2 = dc_mod(mid, b)
    x = (x2 * x1) % P
    z = (x2 * z1 + z2 * x1) % P
    return (x, z)

CHUNKS = 12
M = 1194648
step = M // CHUNKS

for i in range(CHUNKS):
    start = i * step
    end = (i + 1) * step if i != CHUNKS - 1 else M
    x, z = dc_mod(start, end)
    print(f"chunk {i}: start={start} end={end} x={x} z={z}")
