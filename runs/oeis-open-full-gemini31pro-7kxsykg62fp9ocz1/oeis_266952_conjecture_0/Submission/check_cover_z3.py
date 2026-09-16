from z3 import *

# Let's try to cover p with a set of primes Q.
# For each q in Q, we choose a residue c_q = 6n mod q.
# This forbids p = 0, 2, c_q, c_q+2 mod q.
# We want to find c_q for each q such that EVERY p is forbidden by at least one q.
# By CRT, we can just check all p from 0 to Prod(Q)-1.

Q = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]

s = Solver()
c = {q: Int(f'c_{q}') for q in Q}

for q in Q:
    s.add(c[q] >= 0, c[q] < q)
    # c_q must be a valid 6n mod q. Since 6 is coprime to q > 3, it can be anything.
    # For q=2, 6n = 0 mod 2. So c_2 = 0.
    if q == 2:
        s.add(c[q] == 0)
    # For q=3, 6n = 0 mod 3. So c_3 = 0.
    if q == 3:
        s.add(c[q] == 0)

# We want: ForAll p in 0..Prod(Q)-1, Or_{q} (p%q == 0, p%q == 2, p%q == c_q, p%q == (c_q+2)%q)
# Instead of ForAll, since p%q are independent, this is equivalent to saying:
# There is NO tuple of valid residues (v_q) for each q.
# But as I proved, for q>=5, there are at least q-4 > 0 valid residues.
# So a tuple (v_q) ALWAYS exists!
# Let's print the number of valid residues for each q to be absolutely sure.
for q in Q:
    print(f"q={q}")
    for cq in range(q):
        valid = 0
        for p in range(q):
            if p%q != 0 and p%q != 2 and p%q != cq and p%q != (cq+2)%q:
                valid += 1
        print(f"  cq={cq}: {valid} valid residues")
