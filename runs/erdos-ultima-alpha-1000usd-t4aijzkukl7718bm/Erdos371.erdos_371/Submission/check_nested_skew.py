"""Diagnostic only: optimize a proposed finite skew bound for nested prime sets.
This does not search for a counterexample to Erdos 371 or certify a Lean theorem.
Run using sage -python.
"""
import json, sys
from sage.all import MixedIntegerLinearProgram, prime_range, prime_divisors

N = int(sys.argv[1])
primes = list(prime_range(N+2))
m = MixedIntegerLinearProgram(maximization=True, solver='GLPK')
f = m.new_variable(binary=True)
g = m.new_variable(binary=True)
r = m.new_variable(binary=True)
s = m.new_variable(binary=True)
for p in primes:
    m.add_constraint(f[p] <= g[p])
for n in range(1,N+2):
    ps = list(prime_divisors(n))
    if not ps:
        m.add_constraint(f[n] == 1)
        m.add_constraint(g[n] == 1)
    elif len(ps) != 1 or ps[0] != n:
        for p in ps:
            m.add_constraint(f[n] <= f[p])
            m.add_constraint(g[n] <= g[p])
        m.add_constraint(f[n] >= sum(f[p] for p in ps) - len(ps) + 1)
        m.add_constraint(g[n] >= sum(g[p] for p in ps) - len(ps) + 1)
for n in range(1,N+1):
    m.add_constraint(r[n] <= f[n])
    m.add_constraint(r[n] <= g[n+1])
    m.add_constraint(r[n] >= f[n]+g[n+1]-1)
    m.add_constraint(s[n] <= g[n])
    m.add_constraint(s[n] <= f[n+1])
    m.add_constraint(s[n] >= g[n]+f[n+1]-1)
m.set_objective(sum(r[n]-s[n] for n in range(1,N+1)))
m.solver_parameter('timelimit', 45)
status = 'solver returned; optimality is not certified'
try:
    val = m.solve()
except Exception as e:
    status = str(e)
try:
    fv = m.get_values(f)
    gv = m.get_values(g)
    F = [int(p) for p in primes if fv[p] > .5]
    G = [int(p) for p in primes if gv[p] > .5]
    fs, gs = set(F), set(G)
    ff = lambda n: int(set(prime_divisors(n)) <= fs)
    gg = lambda n: int(set(prime_divisors(n)) <= gs)
    v = sum(ff(n)*gg(n+1)-gg(n)*ff(n+1) for n in range(1,N+1))
    print(json.dumps({'N':N, 'prime_count':len(primes), 'status':status, 'value':v, 'F':F, 'G':G}))
except Exception as e:
    print(json.dumps({'N':N, 'prime_count':len(primes), 'status':status, 'extraction_error':str(e)}))
