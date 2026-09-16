def check_mod(q):
    # we want to see if there's any n where for all p,
    # p is 0, 2, 6n, or 6n+2 mod q
    for n in range(q):
        covered = True
        for p in range(q):
            if p%q != 0 and (p-2)%q != 0 and (6*n-p)%q != 0 and (6*n+2-p)%q != 0:
                covered = False
                break
        if covered:
            print(f"Modulus {q} has a full cover at n = {n}!")
            return True
    return False

for q in range(2, 100):
    if all(q%i != 0 for i in range(2, q)):
        check_mod(q)
