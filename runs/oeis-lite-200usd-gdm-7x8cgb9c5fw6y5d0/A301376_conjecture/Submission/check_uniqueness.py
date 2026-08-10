import sys

N = 1048576
N2 = N * N

def get_V_all(N2):
    V = {1}
    for s in range(10):
        fs = (10 * 16**s + 16 * 4**s + 10) // 9
        for i in range(20):
            val = fs * 4**i
            if val < N2:
                V.add(val)
    return sorted(list(V))

V_all = get_V_all(N2)
print("V_all size:", len(V_all))

mapping = {}
for v in V_all:
    if v == 1:
        continue
    # Find all (s, i) that give v
    pairs = []
    for s in range(10):
        fs = (10 * 16**s + 16 * 4**s + 10) // 9
        for i in range(20):
            if fs * 4**i == v:
                pairs.append((s, i))
    print(f"v = {v}: pairs = {pairs}")
    if len(pairs) != 1:
        print(f"Error! Non-unique representation for v = {v}: {pairs}")
        sys.exit(1)

print("SUCCESS! Every element has a unique representation!")
