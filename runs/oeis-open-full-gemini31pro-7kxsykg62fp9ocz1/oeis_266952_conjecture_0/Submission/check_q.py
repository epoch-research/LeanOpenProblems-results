def valid_count(n, q):
    count = 0
    for p in range(q):
        if p%q != 0 and (p-2)%q != 0 and (6*n-p)%q != 0 and (6*n+2-p)%q != 0:
            count += 1
    return count

def check_all():
    primes = [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199]
    for q in primes:
        mc = min(valid_count(n, q) for n in range(q))
        if mc == 0:
            print(f"Modulus {q} has a local obstruction!")
            return
    print("No local obstruction for q up to 200.")

check_all()
