import math

def compute_A_with_C(n, C):
    def choose(m, k):
        if k >= 6: return 0
        if m == 0: return 1 if k == 0 else 0
        return C[m % 6][k]
    
    total = 0
    for n1 in range(n + 1):
        for n2 in range(n - n1 + 1):
            term = (choose(n, n1) * choose(n - n1, n2)) ** 3
            total += term
    return total

C = [[0]*6 for _ in range(6)]
for m in range(5):
    for k in range(6):
        if k <= m:
            C[m][k] = math.comb(m, k)

# Let's search C[5] in a wider range
for c1 in range(0, 5):
    for c2 in range(0, 5):
        for c3 in range(0, 5):
            for c4 in range(0, 5):
                for c5 in range(0, 5):
                    C[5] = [1, c1, c2, c3, c4, c5]
                    a1 = compute_A_with_C(13, C)
                    a5 = compute_A_with_C(17, C)
                    a2 = compute_A_with_C(14, C)
                    a4 = compute_A_with_C(16, C)
                    if a1 == a5 and a2 == a4:
                        print(f"C[5] = {C[5]}, a1={a1}, a2={a2}")
