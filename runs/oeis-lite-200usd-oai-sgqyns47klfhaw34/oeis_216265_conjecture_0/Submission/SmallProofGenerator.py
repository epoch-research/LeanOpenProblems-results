import sympy as sp
for n in range(14,200):
    N=n**3
    p=sp.nextprime(N-n)
    if p>N: print('fail',n); break
    print(f'| {n} => exact A_pos_of_exists_prime (n:={n}) (p:={int(p)}) (by norm_num) (by norm_num) (by norm_num)')
