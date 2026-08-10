def precompute_V():
    V = {1}
    for s in range(40):
        fs = (10 * 16**s + 16 * 4**s + 10) // 9
        for i in range(160):
            val = fs * 4**i
            V.add(val)
    return sorted(list(V))

all_V = precompute_V()

min_unblocked = 9999
best_N = None
unblocked_at_best = []

print("Running distribution check...")
for N in range(100001, 150000, 2):
    N2 = N * N
    V_actual = [v for v in all_V if v < N2]
    
    unblocked = []
    for v in V_actual:
        diff = N2 - v
        # check if diff is a sum of two squares
        # a number is a sum of two squares iff all its prime factors p = 3 mod 4 have even exponents
        factors = factor(diff)
        is_sq_sum = True
        for p, exp in factors:
            if p % 4 == 3 and exp % 2 != 0:
                is_sq_sum = False
                break
        if is_sq_sum:
            unblocked.append(v)
            
    if len(unblocked) < min_unblocked:
        min_unblocked = len(unblocked)
        best_N = N
        unblocked_at_best = list(unblocked)
        print(f"New best N = {N}: {min_unblocked} unblocked elements.")
        if min_unblocked == 0:
            print("FOUND COUNTEREXAMPLE!")
            break
            
print(f"Finished. Min unblocked elements: {min_unblocked} at N = {best_N}")
if min_unblocked > 0:
    print(f"Unblocked elements at best N: {unblocked_at_best}")
