import sympy

def generate_mod_proofs():
    limit = 15000000
    is_prime = [True] * limit
    is_prime[0] = is_prime[1] = False
    for i in range(2, int(sympy.integer_nthroot(limit, 2)[0]) + 1):
        if is_prime[i]:
            for j in range(i*i, limit, i):
                is_prime[j] = False
    primes = [i for i, p in enumerate(is_prime) if p]

    def qr(m):
        return set((x*x)%m for x in range(m))

    moduli = [3, 4, 5, 7, 8, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53]
    residues = {m: qr(m) for m in moduli}

    proofs = []
    for n in range(40, 3000):
        start = n*(n-1)//2
        if start + n > len(primes): break
        val = sum(primes[start : start + n])
        proved = False
        for m in moduli:
            if (val % m) not in residues[m]:
                # proved using modulo m!
                proofs.append((n, val, m, val % m))
                proved = True
                break
        if not proved:
            print(f"FAILED TO PROVE n = {n}")
            return None
    return proofs

proofs = generate_mod_proofs()
if proofs:
    print(f"Generated {len(proofs)} proofs successfully.")
    # let's write out some of them
    for i in range(10):
        print(proofs[i])
