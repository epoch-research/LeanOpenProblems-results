import sympy

with open('/workspace/leanproject/Submission/PrimeProof.lean', 'w') as f:
    f.write('import Mathlib\nopen Nat\n\n')
    
    c = 0
    chunk_size = 300
    total = 7854
    
    boundaries = list(range(chunk_size, total, chunk_size))
    if 7841 not in boundaries:
        boundaries.append(7841)
    if 7853 not in boundaries:
        boundaries.append(7853)
    if total not in boundaries:
        boundaries.append(total)
    boundaries.sort()
    
    start = 0
    for end in boundaries:
        f.write(f'lemma c_{end} : count Nat.Prime {end} = {sympy.primepi(end-1)} := by\n')
        if start == 0:
            f.write('  have c0 : count Nat.Prime 0 = 0 := count_zero (p := Nat.Prime)\n')
        else:
            f.write(f'  have c{start} : count Nat.Prime {start} = {c} := c_{start}\n')
        
        for i in range(start, end):
            if sympy.isprime(i):
                f.write(f'  have p{i} : Nat.Prime {i} := by norm_num\n')
                f.write(f'  have c{i+1} : count Nat.Prime {i+1} = {c+1} := by rw [count_succ, c{i}, if_pos p{i}]\n')
                c += 1
            else:
                f.write(f'  have p{i} : ¬ Nat.Prime {i} := by norm_num\n')
                f.write(f'  have c{i+1} : count Nat.Prime {i+1} = {c} := by rw [count_succ, c{i}, if_neg p{i}]\n')
        f.write(f'  exact c{end}\n\n')
        start = end
    
    # Now prove P991 = 7841 and P992 = 7853
    f.write('lemma p991 : Nat.nth Nat.Prime 990 = 7841 := by\n')
    f.write('  have h1 : Nat.Prime 7841 := by norm_num\n')
    f.write('  have h2 : count Nat.Prime 7841 = 990 := c_7841\n')
    f.write('  have h3 := Nat.nth_count h1\n')
    f.write('  rw [h2] at h3\n')
    f.write('  exact h3\n\n')
    
    f.write('lemma p992 : Nat.nth Nat.Prime 991 = 7853 := by\n')
    f.write('  have h1 : Nat.Prime 7853 := by norm_num\n')
    f.write('  have h2 : count Nat.Prime 7853 = 991 := c_7853\n')
    f.write('  have h3 := Nat.nth_count h1\n')
    f.write('  rw [h2] at h3\n')
    f.write('  exact h3\n\n')
