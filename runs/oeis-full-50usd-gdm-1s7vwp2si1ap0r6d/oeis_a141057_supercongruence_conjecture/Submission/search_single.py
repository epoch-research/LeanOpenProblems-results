def factorization(n):
    if n <= 1: return {}
    factors = {}
    d_val = 2
    temp = n
    while d_val * d_val <= temp:
        while (temp % d_val) == 0:
            factors[d_val] = factors.get(d_val, 0) + 1
            temp //= d_val
        d_val += 1
    if temp > 1:
        factors[temp] = factors.get(temp, 0) + 1
    return factors

def d(m):
    if m == 0: return 0
    f = factorization(m)
    return (2 ** f.get(2, 0)) * (3 ** f.get(3, 0))

is_smooth = [d(i) == i for i in range(21)]

A_val = {0: 1, 1: 3, 2: 27, 3: 381, 4: 6219}
c = [0] * 21

def get_A(m, c_curr):
    if m in A_val:
        return A_val[m]
    if m == 5:
        return 1 + 347 * (c_curr[5] ** 3)
    else:
        return 1 + (c_curr[m] ** 3) * (2 + c_curr[m-1] ** 3)

def solve(m):
    if m > 20:
        return True
    
    dm = d(m)
    if is_smooth[m]:
        for cm_val in range(0, 10):
            c[m] = cm_val
            A_val[m] = get_A(m, c)
            if solve(m + 1):
                return True
            del A_val[m]
    else:
        target = A_val[dm]
        bracket = 347 if m == 5 else (2 + c[m-1] ** 3)
        # We need 1 + c[m]^3 * bracket = target
        # So c[m]^3 * bracket = target - 1
        rem = target - 1
        if rem % bracket == 0:
            val3 = rem // bracket
            cm_val = round(val3 ** (1/3))
            if cm_val ** 3 == val3:
                c[m] = cm_val
                A_val[m] = target
                if solve(m + 1):
                    return True
                del A_val[m]
    return False

if solve(5):
    for m in range(5, 21):
        print(f"m={m}: c={c[m]}, A={A_val[m]}")
else:
    print("No solution found!")
