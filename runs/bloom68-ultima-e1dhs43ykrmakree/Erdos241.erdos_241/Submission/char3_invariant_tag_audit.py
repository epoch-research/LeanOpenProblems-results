#!/usr/bin/env python3
"""EXACT q=27 characteristic-three Singer audit; orbit variables, not point tags.

Python standard library only. No existing audit is imported or modified.
New solver calls, including core extraction, share a persistent 300s ledger.
Commands: construct, prepare, run. Independent checking: char3_invariant_tag_verify.py.
"""
from __future__ import annotations
import argparse
from collections import Counter, defaultdict
import gzip
import hashlib
import itertools as it
import json
import math
from pathlib import Path
import subprocess
import tempfile
import time

HERE = Path(__file__).resolve().parent
OUT = HERE / 'char3_invariant_tag_results'
PREFIX = 'char3_invariant_tag_'
BINARY = Path(tempfile.gettempdir()) / (PREFIX + 'solver')
Q, V, K, M = 27, 757, 13, 9841


def sha(b):
    return hashlib.sha256(b).hexdigest()


def write_json(path, obj):
    path.parent.mkdir(parents=True, exist_ok=True)
    temp = path.with_suffix(path.suffix + '.tmp')
    temp.write_text(json.dumps(obj, indent=2) + '\n')
    temp.replace(path)


def data_path(name):
    return OUT / (PREFIX + name)


class Tower:
    """F3[u,theta]/(u^3-u-1, theta^3-theta-2u^2).

    F27 encoding: b0+3b1+9b2. Tower encoding: x0+27x1+729x2.
    Multiplication uses polynomial convolution and top-down reduction.
    """
    def __init__(self):
        self.digits = [(x % 3, x//3 % 3, x//9) for x in range(27)]
        self.add27 = [[sum((a+b) % 3 * 3**j for j, (a,b) in enumerate(zip(self.digits[x], self.digits[y])))
                       for y in range(27)] for x in range(27)]
        self.neg27 = [sum((-a) % 3 * 3**j for j,a in enumerate(self.digits[x])) for x in range(27)]
        self.mul27 = [[self.product27(x, y) for y in range(27)] for x in range(27)]
        self.a = 18

    def product27(self, x, y):
        c = [0]*5
        for i,a in enumerate(self.digits[x]):
            for j,b in enumerate(self.digits[y]):
                c[i+j] += a*b
        # u^3 = u+1
        for d in (4,3):
            c[d-3] += c[d]
            c[d-2] += c[d]
        return sum(c[j] % 3 * 3**j for j in range(3))

    @staticmethod
    def decode(x):
        return x % 27, x//27 % 27, x//729

    def add(self, *xs):
        c = [0,0,0]
        for x in xs:
            for j,a in enumerate(self.decode(x)):
                c[j] = self.add27[c[j]][a]
        return sum(a*27**j for j,a in enumerate(c))

    def mul(self, x, y):
        c = [0]*5
        for i,a in enumerate(self.decode(x)):
            for j,b in enumerate(self.decode(y)):
                c[i+j] = self.add27[c[i+j]][self.mul27[a][b]]
        # theta^3 = theta+a
        for d in (4,3):
            c[d-3] = self.add27[c[d-3]][self.mul27[self.a][c[d]]]
            c[d-2] = self.add27[c[d-2]][c[d]]
        return sum(c[j]*27**j for j in range(3))

    def power(self, x, n):
        r = 1
        while n:
            if n & 1:
                r = self.mul(r,x)
            x = self.mul(x,x)
            n >>= 1
        return r

    def trace27(self, x):
        return self.add(x,self.power(x,3),self.power(x,9))


def construction():
    f = Tower()
    theta = 27
    assert all((x**3-x-1) % 3 for x in range(3))
    assert f.trace27(f.a) == 1
    assert f.power(theta,3) == f.add(theta,f.a)
    assert f.power(theta,27) == f.add(theta,1)
    assert f.power(theta,729) == f.add(theta,2)
    order = Q**3-1
    factors = [2,13,757]
    g = next(x for x in range(27, Q**3) if all(f.power(x,order//p) != 1 for p in factors))
    assert f.power(g,order) == 1
    gq, gqq = f.power(g,Q), f.power(g,Q*Q)
    z = zq = zqq = 1
    logs, residues, full_logs = [], [], {}
    for e in range(order):
        assert z not in full_logs
        full_logs[z] = e
        tr = f.add(z,zq,zqq)
        assert tr < 27
        if tr == 0:
            residues.append(e % V)
            if e < V:
                logs.append(e)
        z,zq,zqq = f.mul(z,g),f.mul(zq,gq),f.mul(zqq,gqq)
    assert (z,zq,zqq) == (1,1,1)
    S = logs
    assert len(S) == 28 and 0 in S
    assert Counter(residues) == Counter({s:26 for s in S})
    diffs = Counter((s-t) % V for s in S for t in S if s != t)
    assert diffs == Counter({r:1 for r in range(1,V)})
    assert sorted(Q*s % V for s in S) == S
    seen = {0}
    orbits = []
    for s in S:
        if s in seen:
            continue
        points = sorted({s,Q*s % V,Q*Q*s % V})
        assert len(points) == 3 and sum(points) % V == 0
        ts, norm = [], None
        for h in points:
            z = f.power(g,h)
            b0,b1,b2 = f.decode(z)
            assert b2 == 0 and b1 != 0
            t = f.mul(b0,f.power(b1,25))
            assert t < 27
            w = f.add(f.a,f.power(t,3),f.neg27[t])
            assert w == f.power(f.add(theta,t),V) < 27
            assert f.trace27(w) == 1
            assert norm is None or norm == w
            norm = w
            assert full_logs[f.add(theta,t)] % V == h
            ts.append(t)
        assert set(ts) == {ts[0],f.add(ts[0],1),f.add(ts[0],2)}
        orbits.append({'id':len(orbits),'points':points,'t_in_point_order':ts,
                       'norm_a_plus_t3_minus_t':norm,
                       'natural_half_log_tag':full_logs[f.add(theta,ts[0])] % K})
        seen.update(points)
    assert seen == set(S) and len(orbits) == 9
    assert len({o['norm_a_plus_t3_minus_t'] for o in orbits}) == 9
    assert math.gcd(V,K) == 1 and Q % K == 1 and pow(Q,3,M) == 1
    return {'q':Q,'v':V,'k':K,'M':M,'F27_polynomial':'u^3-u-1',
            'tower_polynomial':'theta^3-theta-2*u^2','a_encoded':f.a,
            'theta_encoded':theta,'generator_encoded':g,'generator_coefficients':list(f.decode(g)),
            'order':order,'order_prime_factors':factors,
            'primitive_order_tests':{str(p):f.power(g,order//p) for p in factors},
            'subfield_generator_g_to_v':f.power(g,V),'minus_one_g_to_M':f.power(g,M),
            'encoding':'F27: b0+3*b1+9*b2; K: x0+27*x1+729*x2',
            'S':S,'infinity':0,'orbits':orbits,'perfect_difference_counts':[diffs[r] for r in range(V)],
            'trace_zero_nonzero_elements':len(residues),'full_multiplicative_cycle':len(full_logs),
            'crt_inverse_v_mod_k':pow(V,-1,K),'crt_inverse_k_mod_v':pow(K,-1,V)}


def orient(row):
    row = tuple(row)
    first = next((x for x in row if x),0)
    return tuple(-x for x in row) if first < 0 else row


def families():
    # Exact requested order. No symmetry identification of deletion cases.
    for count, keep_inf in [(1,True),(1,False),(2,True),(2,False)]:
        for deleted in it.combinations(range(9),count):
            yield deleted,keep_inf


def make_instance(c, deleted, keep_inf):
    deleted = tuple(sorted(deleted))
    retained = [o for o in c['orbits'] if o['id'] not in deleted]
    variables = [o['id'] for o in retained] + (['infinity'] if keep_inf else [])
    T = sorted([s for o in retained for s in o['points']] + ([0] if keep_inf else []))
    point_to_orbit = {s:o['id'] for o in retained for s in o['points']}
    if keep_inf:
        point_to_orbit[0] = 'infinity'
    point_variables = [variables.index(point_to_orbit[s]) for s in T]
    r,n = len(variables),len(T)
    fibers = [[] for _ in range(V)]
    for triple in it.combinations_with_replacement(range(n),3):
        counts = [0]*r
        for j in triple:
            counts[point_variables[j]] += 1
        fibers[sum(T[j] for j in triple) % V].append((triple,counts))
    witnesses = {}
    raw = 0
    for h, triples in enumerate(fibers):
        for (left,lc),(right,rc) in it.combinations(triples,2):
            raw += 1
            row = tuple(a-b for a,b in zip(lc,rc))
            canonical = orient(row)
            if row != canonical:
                left,right = right,left
            # A zero row is an immediate certificate, never silently omitted.
            if canonical not in witnesses:
                witnesses[canonical] = {'left':[T[j] for j in left],
                                        'right':[T[j] for j in right],'base_sum':h}
    rows = sorted(witnesses)
    assert all(sum(row) == 0 and max(map(abs,row)) <= 3 for row in rows)
    # All full-orbit products have base sum 0, forcing distinct orbit labels.
    for i,j in it.combinations(range(len(retained)),2):
        row = tuple(3*(int(l==i)-int(l==j)) for l in range(r))
        assert orient(row) in witnesses
    if keep_inf:
        for i in range(len(retained)):
            row = tuple(3*(int(l==i)-int(l==r-1)) for l in range(r))
            assert orient(row) in witnesses
    case = f'n{n}_d' + '_'.join(map(str,deleted))
    return {'case':case,'n':n,'variable_count':r,'variables':variables,
            'deleted_orbits':list(deleted),'keep_infinity':keep_inf,
            'deleted_points':sorted(set(c['S'])-set(T)),'T':T,'point_variables':point_variables,
            'triple_multisets':math.comb(n+2,3),'triple_repeat_counts':
                {'all_equal':n,'exactly_two_equal':n*(n-1),'all_distinct':math.comb(n,3)},
            'raw_collision_pairs':raw,'triple_fiber_histogram':dict(sorted(Counter(map(len,fibers)).items())),
            'row_count':len(rows),'zero_row':([0]*r in [list(row) for row in rows]),
            'rows':rows,'witnesses':[witnesses[row] for row in rows]}


def row_text(r, rows):
    return f'{r} {K} {len(rows)}\n' + ''.join(' '.join(map(str,row))+'\n' for row in rows)


def prepare():
    c = construction()
    write_json(data_path('construction.json'),c)
    records = []
    for deleted,keep_inf in families():
        instance = make_instance(c,deleted,keep_inf)
        text = row_text(instance['variable_count'],instance['rows'])
        path = data_path(instance['case']+'.rows')
        path.write_text(text)
        instance['input_file'] = path.name
        instance['input_sha256'] = sha(text.encode())
        # Store the complete exact model, including a triple witness for every row.
        write_json(data_path(instance['case']+'.json'),instance)
        records.append({key:value for key,value in instance.items() if key not in ('rows','witnesses')})
    write_json(data_path('instances.json'),records)
    print(json.dumps({'instances':len(records),'by_n':dict(Counter(i['n'] for i in records)),
                      'rows_range':[min(i['row_count'] for i in records),max(i['row_count'] for i in records)],
                      'zero_rows':sum(i['zero_row'] for i in records)},indent=2))


class Budget:
    """Conservative sum of wall times of all NEW search processes (not just DFS).

    Each reservation includes an external subprocess deadline. Never use timeout
    as evidence of UNSAT. The saved ledger is shared with any core extraction.
    """
    def __init__(self):
        self.path = data_path('search_ledger.json')
        if self.path.exists():
            self.data = json.loads(self.path.read_text())
        else:
            self.data = {'cap_seconds':300.0,'charges':[],
                         'accounting':'sum of process wall times, including launch/output; solver DFS also reported'}

    @property
    def used(self):
        return sum(x['process_wall_seconds'] for x in self.data['charges'])

    def solve(self, r, rows, name, seconds=5.0):
        if any(x['case'] == name for x in self.data['charges']):
            raise RuntimeError('Search already charged: '+name+'; use a fresh --out directory for replay.')
        remaining = self.data['cap_seconds']-self.used
        if remaining < 0.1:
            return {'status':'UNATTEMPTED_BUDGET'}
        limit = min(seconds,remaining-0.05)
        inpath,proofpath = data_path(name+'.rows'),data_path(name+'.tree')
        text = row_text(r,rows)
        inpath.write_text(text)
        start = time.monotonic()
        try:
            run = subprocess.run([str(BINARY),str(inpath),str(max(1,int((limit-0.02)*1000))),str(proofpath)],
                                 capture_output=True,text=True,timeout=limit,check=True)
            answer = json.loads(run.stdout)
        except subprocess.TimeoutExpired:
            answer = {'status':'TIMEOUT','timeout_kind':'external_process_deadline'}
        elapsed = time.monotonic()-start
        charge = {'case':name,'limit_seconds':limit,'process_wall_seconds':elapsed,
                  'status':answer['status'],'dfs_elapsed_ms':answer.get('elapsed_ms')}
        self.data['charges'].append(charge)
        write_json(self.path,self.data)
        answer.update({'process_wall_seconds':elapsed,'input_file':inpath.name,
                       'input_sha256':sha(text.encode()),'time_limit_seconds':limit})
        if answer['status'] == 'UNSAT':
            raw = proofpath.read_bytes()
            compressed = data_path(name+'.tree.gz')
            compressed.write_bytes(gzip.compress(raw,mtime=0))
            answer.update({'proof':compressed.name,'proof_sha256_uncompressed':sha(raw),
                           'proof_bytes_uncompressed':len(raw)})
            proofpath.unlink()
        return answer


def compile_solver():
    subprocess.run(['g++','-O3','-std=c++17','-Wall','-Wextra','-pedantic',
                    str(HERE/(PREFIX+'solver.cpp')),'-o',str(BINARY)],check=True)


def verify_sat(instance, tags):
    assert len(tags) == instance['variable_count'] and tags[0] == 0
    assert all(0 <= x < K for x in tags)
    T, pv = instance['T'],instance['point_variables']
    point_tags = [tags[j] for j in pv]
    A = [(s+V*((c-s)*pow(V,-1,K) % K)) % M for s,c in zip(T,point_tags)]
    assert len(set(A)) == len(A) and all(x % V == s and x % K == c for x,s,c in zip(A,T,point_tags))
    assert {Q*x % M for x in A} == set(A)
    sums = {}
    for triple in it.combinations_with_replacement(range(len(A)),3):
        h = sum(A[i] for i in triple) % M
        assert h not in sums, (sums.get(h),triple,h)
        sums[h] = triple
    return {'CRT_A_in_T_order':A,'point_tags_in_T_order':point_tags,
            'distinct_parameters':len(set(T)),'distinct_triple_sums':len(sums),
            'strong_B3':True,'actual_cyclic_frobenius_invariant':True}


def run_all():
    if data_path('results.json').exists():
        raise SystemExit('Refusing to overwrite existing results; inspect saved audit/ledger.')
    records = json.loads(data_path('instances.json').read_text())
    compile_solver()
    budget = Budget()
    results = {'scope':'all 9+9+36+36 specified invariant deletion cases at q=27; no case symmetry quotient',
               'normalization':'only the first retained full-orbit tag is set to 0 by translation',
               'instances':[]}
    for record in records:
        instance = json.loads(data_path(record['case']+'.json').read_text())
        answer = budget.solve(instance['variable_count'],instance['rows'],record['case'],seconds=3.0)
        if answer['status'] == 'SAT':
            answer['verification'] = verify_sat(instance,answer['tags'])
        result = dict(record,**answer)
        results['instances'].append(result)
        results['summary'] = {'by_n':{str(n):dict(Counter(x['status'] for x in results['instances'] if x['n']==n))
                                      for n in [25,24,22,21]},
                              'search_process_wall_seconds':budget.used,
                              'dfs_seconds':sum(x.get('elapsed_ms',0) for x in results['instances'])/1000,
                              'cap_seconds':300.0}
        write_json(data_path('results.json'),results)
        print(record['case'],answer['status'],answer.get('nodes','-'),f'budget used {budget.used:.4f}s',flush=True)
    print(json.dumps(results['summary'],indent=2),flush=True)


def main():
    global OUT
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command',choices=['construct','prepare','run'])
    parser.add_argument('--out',type=Path,default=OUT,help='use a fresh directory to replay the audit')
    args = parser.parse_args()
    OUT = args.out.resolve()
    OUT.mkdir(parents=True,exist_ok=True)
    if args.command == 'construct':
        c = construction()
        write_json(data_path('construction.json'),c)
        print(json.dumps(c,indent=2))
    elif args.command == 'prepare':
        prepare()
    else:
        run_all()


if __name__ == '__main__':
    main()
