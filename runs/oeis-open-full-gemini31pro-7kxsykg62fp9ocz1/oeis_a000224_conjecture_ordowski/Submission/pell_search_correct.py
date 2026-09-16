import math

def issq(n):
    if n < 0: return False
    r = int(math.isqrt(n))
    return r*r == n

for Q in range(1, 16):
    C = Q*(Q-12)//4
    for W in range(2, 5000000):
        Z2 = (16-Q)*W*W + C
        if issq(Z2):
            Z = math.isqrt(Z2)
            for sign in [1, -1]:
                num = 16*W + sign * 4 * Z
                if num % (2*Q) == 0:
                    X = num // (2*Q)
                    P = X - W
                    S = W + 1
                    V2 = S*S - 4*P
                    if issq(V2):
                        V = math.isqrt(V2)
                        if (S + V) % 2 == 0:
                            p = (S + V) // 2
                            q = (S - V) // 2
                            if p > 1 and q > 1:
                                print(f"Found! p={p}, q={q}, Q={Q}, W={W}")
