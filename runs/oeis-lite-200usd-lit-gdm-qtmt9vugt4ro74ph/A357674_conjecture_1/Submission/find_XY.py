def choose(n, k):
    import math
    return math.comb(n, k)

def find_XY(p):
    S1 = sum(choose(p + k - 1, k) for k in range(2 * p + 1))
    S2 = sum(choose(p + k - 1, k)**2 for k in range(2 * p + 1))
    X = ((S1 - 3) // (p**3)) % (p**2)
    Y = ((S2 - 3) // (p**3)) % (p**2)
    # Let's print as signed integers in [-p^2/2, p^2/2]
    X_signed = X if X < p**2 / 2 else X - p**2
    Y_signed = Y if Y < p**2 / 2 else Y - p**2
    print(f"p = {p:2d}: X ≡ {X_signed:4d}, Y ≡ {Y_signed:4d} (mod {p**2})")

for p in [5, 7, 11, 13, 17]:
    find_XY(p)
