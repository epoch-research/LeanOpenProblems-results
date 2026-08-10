def s_q(x, q):
    s = 0
    while x > 0:
        s += x % q
        x //= q
    return s

def v_q(k, q):
    # For a(2k+1), the prime valuation of the factorial ratio at q is:
    # ( s_q(8*k+4, q) + s_q(2*k+1, q) + s_q(3*k+1, q) - s_q(4*k+2, q) - s_q(9*k+4, q) ) / (q - 1)
    val = s_q(8*k+4, q) + s_q(2*k+1, q) + s_q(3*k+1, q) - s_q(4*k+2, q) - s_q(9*k+4, q)
    return val

# Let us search for ANY k < 5000 and any prime q < 10000 where v_q(k, q) < 0
import sympy
primes = list(sympy.primerange(3, 10000))

print("Searching for counterexample to integrality of a(2k+1)...")
found = False
for k in range(1000):
    for q in primes:
        if q > 9*k + 4:
            break
        val = v_q(k, q)
        if val < 0:
            print(f"FOUND COUNTEREXAMPLE: k={k} (n={2*k+1}), q={q}, valuation numerator={val}")
            found = True
            break
    if found:
        break
else:
    print("No counterexample found for k < 1000 and q < 10000!")
