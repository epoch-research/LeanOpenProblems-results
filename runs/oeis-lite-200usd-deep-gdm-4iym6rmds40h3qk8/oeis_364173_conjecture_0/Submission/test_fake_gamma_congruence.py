import sympy
from sympy import S

S_set = {2, S(5)/2, 3, 4, 5, S(11)/2, 6, 10, 11, 16, S(17)/2, 21, S(47)/2, 46}

# f(x) under our 14-element set S
def f_val(x):
    if x == 2: return S(1)
    elif x == S(5)/2: return S(24)/32
    elif x == 3: return S(2)
    elif x == 4: return S(6)
    elif x == 5: return S(24)
    elif x == S(11)/2: return S(3628800)/122880
    elif x == 6: return S(120)
    elif x == 10: return S(362880)
    elif x == 11: return S(3628800)
    elif x == 16: return S(1307674368000)
    elif x == S(17)/2: return S(20922789888000)/2642411520
    elif x == 21: return S(2432902008176640000)
    elif x == S(47)/2: return S(5502622159812088949850305428800254892961651752960000000000)/1819173952375284468523400649768960000
    elif x == 46: return S(119622220865480194561963161495657715064383733760000000000)
    else: return S(1)

def a(n):
    n_r = S(n)
    num = f_val(9 * n_r + 1) * f_val(2 * n_r + 1) * f_val(S(3)/2 * n_r + 1)
    den = f_val(S(9)/2 * n_r + 1) * f_val(4 * n_r + 1) * f_val(3 * n_r + 1) * f_val(n_r + 1)
    return num / den

# Check if a(n) is always an integer for all n
print("Checking if a(n) is integer for n up to 100...")
all_int = True
for n in range(1, 100):
    val = a(n)
    if val.denominator != 1:
        # print(f"n={n} is NOT integer: {val}")
        all_int = False

print(f"All integers: {all_int}")

# Check congruence for p >= 5, n, r
print("Checking congruence...")
all_cong = True
for p in [5, 7, 11, 13]:
    for n in range(1, 20):
        for r in [1, 2]:
            v1 = a(n * p**r)
            v2 = a(n * p**(r-1))
            mod = p**(3*r)
            if v1.denominator != 1 or v2.denominator != 1:
                # if they are not integers, we can't do % mod directly,
                # but in Lean, Classical.choose is only used if we assume h_int,
                # so we only care about cases where they are integers!
                continue
            diff = v1 - v2
            if diff % mod != 0:
                print(f"FAILED: p={p}, n={n}, r={r}, diff={diff}, mod={mod}")
                all_cong = False

print(f"All congruent: {all_cong}")
