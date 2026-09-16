import math

def issq(n):
    if n < 0: return False
    r = int(math.isqrt(n))
    return r*r == n

for Q in range(1, 200):
    if Q % 4 != 0 and (Q*(12-Q)) % 4 != 0:
        continue
    C = Q*(12-Q)//4
    for W in range(2, 500000):
        Z2 = (16+Q)*W*W + C
        if issq(Z2):
            Z = math.isqrt(Z2)
            for sign in [1, -1]:
                num = (16-Q)*W + sign * 4 * Z
                if num % Q == 0:
                    P = num // Q
                    S = W + 1
                    V2 = S*S - 4*P
                    if issq(V2):
                        V = math.isqrt(V2)
                        if (S + V) % 2 == 0:
                            p = (S + V) // 2
                            q = (S - V) // 2
                            if p > 0 and q > 0:
                                print(f"Found! p={p}, q={q}, Q={Q}, W={W}")
