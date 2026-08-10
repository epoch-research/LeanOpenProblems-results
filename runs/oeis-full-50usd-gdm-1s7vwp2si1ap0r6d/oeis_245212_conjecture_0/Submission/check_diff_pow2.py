import sympy

def divisors(m):
    return sympy.divisors(m)

def tau(m):
    return len(divisors(m))

found = False
for m in range(3, 100001, 2):
    divs = divisors(m)
    C = sum(c * tau(c) for c in divs)
    S = sum(divs)
    diff = C - S
    if diff > 0 and (diff & (diff - 1) == 0):
        print(f"Found C(m) - S(m) is a power of 2: m={m}, C-S={diff}")
        found = True

if not found:
    print("C(m) - S(m) is NEVER a power of 2 for odd m >= 3 up to 100,000!")
