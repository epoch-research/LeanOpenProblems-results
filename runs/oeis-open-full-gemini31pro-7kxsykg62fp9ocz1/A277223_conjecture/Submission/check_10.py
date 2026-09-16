def S(m):
    return sum(int(c) for c in str(m))

def check():
    import itertools
    # sum of digits of 10n is 10. So sum of digits of n is 10.
    # checking n formed by up to 12 digits summing to 10.
    def gen(rem, length, current):
        if length == 0:
            if rem == 0:
                n = int("".join(map(str, current)))
                max_k = 0
                for k in range(1, 200):
                    if S(k * n) == k:
                        max_k = k
                if max_k == 10:
                    print(f"Counterexample! n={n}, max_k=10")
                    exit(0)
            return
        for i in range(10):
            if i <= rem:
                if current == [] and i == 0 and length > 1:
                    continue
                gen(rem - i, length - 1, current + [i])

    for length in range(1, 14):
        gen(10, length, [])
    print("No counterexample up to 13 digits.")

check()
