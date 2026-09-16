def check():
    for p in range(3, 1000, 2):
        for q in range(p, 1000000, 2):
            if (16 * (p+q) * (p+q+2)) % ((p+1)*(q+1)) == 0:
                # also check the other condition
                P = p*q
                S = p+q
                if (16*(S-2)*(S-4)) % (P+S-3) == 0:
                    print(f"Candidate: p={p}, q={q}")
check()
