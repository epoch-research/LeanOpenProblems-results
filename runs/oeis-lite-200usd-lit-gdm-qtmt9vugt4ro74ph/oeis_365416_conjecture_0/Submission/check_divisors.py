import math

divisors = [4, 7, 9, 12, 14, 18, 21, 28, 36, 42, 63, 84, 126, 252]

def has_solution(r, M, p=3):
    # we want to see if there is any f_val >= 2, e_val >= 3
    # such that (r^f - p^e - 2) % M == 0.
    # Since it's modular arithmetic, f_val and e_val are periodic.
    # The period of r mod M is at most M.
    # The period of p mod M is at most M.
    # So we can just check f_val in range(2, M+2) and e_val in range(3, M+3).
    for f_val in range(2, M + 2):
        for e_val in range(3, M + 3):
            if (pow(r, f_val, M) - pow(p, e_val, M) - 2) % M == 0:
                return True
    return False

coprime_rs = [r for r in range(252) if math.gcd(r, 252) == 1]
print(f"Total coprime rs: {len(coprime_rs)}")

no_mod_found = []
for r in coprime_rs:
    found = False
    for M in divisors:
        if math.gcd(r, M) != 1:
            continue
        if not has_solution(r, M, p=3):
            print(f"r = {r}: ruled out by M = {M}")
            found = True
            break
    if not found:
        no_mod_found.append(r)

print("Coprime rs with no divisor found:", no_mod_found)
