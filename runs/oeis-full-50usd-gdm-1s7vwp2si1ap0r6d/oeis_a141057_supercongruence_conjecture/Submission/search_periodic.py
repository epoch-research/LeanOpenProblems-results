import math
import random

# We want to find a 12x12 table C of natural numbers.
# choose(m, k) = C[m % 12][k] if k < 12 else 0.
# We want:
# 1. A(1)=3, A(2)=27, A(3)=381, A(4)=6219.
# 2. A(n * p^k) = A(n * p^(k-1)) for all p >= 5, k >= 1, n >= 1.
# Specifically, we want A(m) to depend only on m % 12, or more generally,
# A(n * p) = A(n) for all p >= 5 and n >= 1.

# Since choose(m, k) for m <= 4 must match Nat.choose(m, k),
# we must have C[m][k] = math.comb(m, k) for m <= 4 and k < 12.
# Also, choose(0, 0) = 1.

# Let's write a solver.
# Since C[m][k] is fixed for m <= 4, we have free variables for m in [5, 11] and k in [0, 11].
# Actually, since choose(m, k) = 0 for k > m, maybe we can assume C[m][k] = 0 for k > m?
# No, we can allow C[m][k] to be anything.
# Let's first check if there exists any C[m][k] for m in [5, 11] such that
# A(n * p) == A(n) for n in [1, 2, 3, 4] and p in [5, 7, 11].
# Note:
# n * p for n in [1, 2, 3, 4] and p in [5, 7, 11]:
# - n=1: 5, 7, 11. (d(5)=1, d(7)=1, d(11)=1). So we want A(5) = A(7) = A(11) = 3.
# - n=2: 10, 14, 22. (d=2). So A(10) = A(14) = A(22) = 27.
# - n=3: 15, 21, 33. (d=3). So A(15) = A(21) = A(33) = 381.
# - n=4: 20, 28, 44. (d=4). So A(20) = A(28) = A(44) = 6219.

# Let's write a function to compute A(n) given C.
def compute_A_with_C(n, C):
    def choose(m, k):
        if k >= 12: return 0
        return C[m % 12][k]
    
    total = 0
    for n1 in range(n + 1):
        for n2 in range(n - n1 + 1):
            term = (choose(n, n1) * choose(n - n1, n2)) ** 3
            total += term
    return total

# Initialize C
C = [[0]*12 for _ in range(12)]
for m in range(5):
    for k in range(12):
        if k <= m:
            C[m][k] = math.comb(m, k)

# We want to fill C[5..11][0..11].
# To make it simple, what if C[m][k] is 0 for k > m?
# Yes, let's assume C[m][k] = 0 for k > m.
# Also, to make things easier, what if C[m][k] only has non-zero values for k = 0, 1, m?
# Actually, let's write a randomized or systematic search for C.
# Since we only want A(m) = A(m % 12), let's see.
# If A(m) is periodic with period 12, then A(5)=A(5 % 12)=A(5)=3.
# A(7)=A(7)=3.
# A(10)=A(10)=27.
# A(11)=A(11)=3.
# A(15)=A(3)=381.
# A(20)=A(8)=A(4)=6219 (if 8 and 4 are in the same orbit, yes, orbit of 4 is {4, 8}).
# So we want:
# A(5) = 3
# A(7) = 3
# A(11) = 3
# A(10) = 27
# A(8) = 6219
# A(9) = 381 (since 9 and 3 are in the same orbit {3, 9})
# So we need A(m) to be constant on the orbits of (Z/12Z)*.
# Let's search for C[5], C[6], C[7], C[8], C[9], C[10], C[11].
# Since A(5) only depends on C[0..5], we can solve for C[5] first!
# Once C[5] is found, A(6) depends on C[0..6], so we can solve for C[6].
# Then C[7], then C[8], ..., then C[11].
# This is a perfect sequential search!

# Let's do this sequentially!
# We want:
# A(5) = 3
# A(6) = any (since 6 is its own orbit)
# A(7) = 3
# A(8) = 6219 (since 8 is in orbit of 4)
# A(9) = 381 (since 9 is in orbit of 3)
# A(10) = 27 (since 10 is in orbit of 2)
# A(11) = 3 (since 11 is in orbit of 1)

targets = {
    5: 3,
    7: 3,
    8: 6219,
    9: 381,
    10: 27,
    11: 3
}

# We can search for each row C[m] (for m = 5..11) to satisfy the target A(m).
# Since C[m][k] can be anything, let's try to restrict C[m][k] to be non-zero only for k in [0, 1, m].
# Or k in [0, 1, 2].
# Let's write a solver that searches for C[m] for each m in 5..11.

def solve_row(m):
    if m > 11:
        # Check if this C actually satisfies A(n * p) == A(n) for larger values?
        # If A(m) is periodic with period 12, then yes, it satisfies it for all.
        # But wait! Is A(n) periodic with period 12?
        # Let's check for n up to 24.
        periodic = True
        for n in range(1, 25):
            val = compute_A_with_C(n, C)
            orbit_rep = {
                1: 1, 5: 1, 7: 1, 11: 1,
                2: 2, 10: 2,
                3: 3, 9: 3,
                4: 4, 8: 4,
                6: 6,
                0: 0
            }[n % 12]
            target = compute_A_with_C(orbit_rep, C) if orbit_rep != n else val
            if val != target:
                periodic = False
                break
        if periodic:
            return True
        return False

    # Try different values for C[m].
    # To keep it simple, let's try C[m][k] for k <= m.
    # What if we restrict to C[m][k] having only 2 non-zero elements?
    # e.g. C[m][0] = 1, and C[m][k] for some k.
    target_val = targets.get(m, None)
    
    # Try all combinations of C[m][k]
    # To make search fast, let's try C[m][k] where only a few k are non-zero.
    # For example, only k = 0, 1, m.
    # Let's try values in [0, 1, 2] for these, or up to 5.
    for c0 in [1]: # usually choose(m, 0) = 1
        for c1 in range(0, 4):
            for cm in range(0, 4):
                # Set C[m]
                C[m] = [0]*12
                C[m][0] = c0
                C[m][1] = c1
                C[m][m] = cm
                
                # If m is smooth (6), we don't have a fixed target, but we want to choose a value.
                # Let's try small values for C[6].
                if target_val is None:
                    if solve_row(m + 1):
                        return True
                else:
                    if compute_A_with_C(m, C) == target_val:
                        if solve_row(m + 1):
                            return True
    return False

if solve_row(5):
    print("Found periodic C:")
    for row in C:
        print(row)
else:
    print("No periodic C found with this restriction.")
