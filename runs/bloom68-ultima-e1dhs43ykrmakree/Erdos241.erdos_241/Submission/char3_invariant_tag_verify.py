#!/usr/bin/env python3
"""Independent exact verifier. Does not import the audit or invoke its solver.

Rebuilds GF(3^9) as F3[X]/(X^9-X^6-X^4-X^2-X+1), not a tower;
walks the complete primitive cycle; rebuilds ALL repeated triple constraints;
checks every refutation tree using the separately implemented native checker.
SAT is checked directly by cyclic CRT triple sums. Standard library + g++.
"""
from __future__ import annotations
import argparse
from collections import Counter
import gzip
import hashlib
import itertools
import json
import math
from pathlib import Path
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
PREFIX = 'char3_invariant_tag_'
OUT = HERE / (PREFIX+'results')
Q,V,K,M = 27,757,13,9841
CHECKER = Path(tempfile.gettempdir()) / (PREFIX+'tree_checker')


def path(name):
    return OUT/(PREFIX+name)


def load(name):
    return json.loads(path(name).read_text())


def sha(b):
    return hashlib.sha256(b).hexdigest()


class FlatField:
    """Tuples of nine F3 coefficients; independently derived degree-nine relation."""
    zero = (0,)*9
    one = (1,)+(0,)*8
    X = (0,1)+(0,)*7
    # X^9 = X^6+X^4+X^2+X-1
    reduction = ((0,2),(1,1),(2,1),(4,1),(6,1))

    def add(self,*args):
        return tuple(sum(t) % 3 for t in zip(*args))

    def neg(self,x):
        return tuple(-a % 3 for a in x)

    def mul(self,x,y):
        terms = [0]*17
        for i,a in enumerate(x):
            if a:
                for j,b in enumerate(y):
                    terms[i+j] += a*b
        for d in range(16,8,-1):
            t = terms[d] % 3
            for j,c in self.reduction:
                terms[d-9+j] += c*t
        return tuple(a % 3 for a in terms[:9])

    def power(self,x,e):
        a = self.one
        for bit in bin(e)[2:]:
            a = self.mul(a,a)
            if bit == '1':
                a = self.mul(a,x)
        return a

    def __init__(self):
        # w=X^3-X=-u^2; u=w^2+w follows from u^3=u+1.
        w = self.add(self.power(self.X,3),self.neg(self.X))
        self.u = self.add(self.mul(w,w),w)
        self.base = []
        u2 = self.mul(self.u,self.u)
        for encoded in range(27):
            b0,b1,b2 = encoded % 3,encoded//3 % 3,encoded//9
            self.base.append(self.add(tuple(b0*x % 3 for x in self.one),
                                      tuple(b1*x % 3 for x in self.u),
                                      tuple(b2*x % 3 for x in u2)))

    def from_tower(self,e):
        b0,b1,b2 = e % 27,e//27 % 27,e//729
        return self.add(self.base[b0],self.mul(self.base[b1],self.X),
                        self.mul(self.base[b2],self.mul(self.X,self.X)))


def check_construction(c):
    assert (c['q'],c['v'],c['k'],c['M']) == (Q,V,K,M)
    assert V==Q*Q+Q+1 and K==(Q-1)//2 and M==(Q**3-1)//2
    assert math.gcd(V,K)==1 and Q % K==1 and math.gcd(Q,M)==1
    assert c['F27_polynomial']=='u^3-u-1' and c['tower_polynomial']=='theta^3-theta-2*u^2'
    f = FlatField()
    assert f.power(f.u,3)==f.add(f.u,f.one)
    assert len(set(f.base))==27
    assert all(f.power(b,27)==b for b in f.base)
    theta = f.from_tower(c['theta_encoded'])
    a = f.from_tower(c['a_encoded'])
    assert theta==f.X and a==f.neg(f.mul(f.u,f.u))
    assert f.add(a,f.power(a,3),f.power(a,9))==f.one
    assert f.power(theta,3)==f.add(theta,a)
    assert f.power(theta,27)==f.add(theta,f.one)
    assert f.power(theta,729)==f.add(theta,f.neg(f.one))
    g = f.from_tower(c['generator_encoded'])
    assert c['generator_encoded']==sum(x*27**i for i,x in enumerate(c['generator_coefficients']))
    order = 19682
    assert c['order']==order and c['order_prime_factors']==[2,13,757]
    for p in c['order_prime_factors']:
        assert all(p % d for d in range(2,math.isqrt(p)+1))
        t = f.power(g,order//p)
        assert t != f.one and t==f.from_tower(c['primitive_order_tests'][str(p)])
    assert f.power(g,order)==f.one
    gq,gqq = f.power(g,27),f.power(g,729)
    z=zq=zqq=f.one
    log_map,trace_logs = {},[]
    for e in range(order):
        assert z != f.zero and z not in log_map
        log_map[z]=e
        tr = f.add(z,zq,zqq)
        assert tr in f.base
        if tr==f.zero:
            trace_logs.append(e % V)
        z,zq,zqq = f.mul(z,g),f.mul(zq,gq),f.mul(zqq,gqq)
    assert (z,zq,zqq)==(f.one,f.one,f.one) and len(log_map)==3**9-1
    # Every nonzero element lies in this unit cycle, also certifying the quotient is a field.
    S=sorted(set(trace_logs))
    assert len(S)==28 and S==c['S']
    assert Counter(trace_logs)==Counter({s:26 for s in S})
    assert len(trace_logs)==c['trace_zero_nonzero_elements']==728
    assert c['full_multiplicative_cycle']==19682
    assert f.power(g,V)==f.from_tower(c['subfield_generator_g_to_v'])==a
    assert f.power(g,M)==f.from_tower(c['minus_one_g_to_M'])==f.neg(f.one)
    differences=[0]*V
    for s in S:
        for t in S:
            if s != t:
                differences[(s-t) % V]+=1
    assert differences==[0]+[1]*(V-1)==c['perfect_difference_counts']
    assert [s for s in S if Q*s % V==s]==[0] and c['infinity']==0
    orbits=[]
    unseen=set(S)-{0}
    while unseen:
        s=min(unseen)
        o=sorted({s,Q*s % V,Q*Q*s % V})
        assert len(o)==3 and set(o)<=unseen and sum(o) % V==0
        unseen.difference_update(o)
        orbits.append(o)
    assert len(orbits)==9
    ts_seen=set()
    norm_values=[]
    for i,o in enumerate(c['orbits']):
        assert o['id']==i and o['points']==orbits[i]
        assert len(o['t_in_point_order'])==3
        for h,t in zip(o['points'],o['t_in_point_order']):
            assert 0<=t<27 and t not in ts_seen
            ts_seen.add(t)
            z=f.add(theta,f.base[t])
            assert log_map[z] % V==h
            w=f.add(a,f.power(f.base[t],3),f.neg(f.base[t]))
            assert w==f.power(z,V)==f.base[o['norm_a_plus_t3_minus_t']]
            assert f.add(w,f.power(w,3),f.power(w,9))==f.one
            assert log_map[z] % K==o['natural_half_log_tag']
        norm_values.append(o['norm_a_plus_t3_minus_t'])
    assert ts_seen==set(range(27)) and len(set(norm_values))==9
    assert set(norm_values)=={j for j,b in enumerate(f.base) if f.add(b,f.power(b,3),f.power(b,9))==f.one}
    assert c['crt_inverse_v_mod_k']==pow(V,-1,K) and c['crt_inverse_k_mod_v']==pow(K,-1,V)
    return {'primitive_cycle':order,'trace_zero_nonzero_elements':len(trace_logs),
            'singer_points':len(S),'perfect_nonzero_differences':V-1,'full_orbits':len(orbits),
            'affine_parameters_checked':len(ts_seen),'norm_values_trace_one':len(set(norm_values)),
            'independent_field_polynomial':'X^9-X^6-X^4-X^2-X+1'}


def canonical(row):
    sign = next((1 if a>0 else -1 for a in row if a),1)
    return tuple(sign*a for a in row)


def reconstruct(c,record):
    deleted=record['deleted_orbits']
    assert deleted==sorted(set(deleted)) and len(deleted) in (1,2) and set(deleted)<=set(range(9))
    labels={s:o['id'] for o in c['orbits'] if o['id'] not in deleted for s in o['points']}
    if record['keep_infinity']:
        labels[0]='infinity'
    variables=[i for i in range(9) if i not in deleted]+(['infinity'] if record['keep_infinity'] else [])
    T=sorted(labels)
    r,n=len(variables),len(T)
    pv=[variables.index(labels[t]) for t in T]
    assert record['variables']==variables and record['T']==T and record['point_variables']==pv
    assert record['n']==n and record['variable_count']==r
    assert record['deleted_points']==sorted(set(c['S'])-set(T))
    fibers=[[] for _ in range(V)]
    for i in range(n):
        for j in range(i,n):
            for l in range(j,n):
                counts=[0]*r
                for t in [i,j,l]:
                    counts[pv[t]]+=1
                fibers[(T[i]+T[j]+T[l]) % V].append(tuple(counts))
    rows=set()
    raw=0
    for f in fibers:
        for i in range(len(f)):
            for j in range(i+1,len(f)):
                raw+=1
                rows.add(canonical(tuple(x-y for x,y in zip(f[i],f[j]))))
    rows=sorted(rows)
    assert record['triple_multisets']==sum(map(len,fibers))==math.comb(n+2,3)
    assert record['triple_repeat_counts']=={'all_equal':n,'exactly_two_equal':n*(n-1),'all_distinct':math.comb(n,3)}
    assert record['raw_collision_pairs']==raw and record['row_count']==len(rows)
    assert record['zero_row']==((0,)*r in rows)
    assert record['triple_fiber_histogram']=={str(a):b for a,b in sorted(Counter(map(len,fibers)).items())}
    for i,j in itertools.combinations(range(r),2):
        # Infinity, when present, also has the base-zero repeated triple (0,0,0).
        distinct=tuple(3*(int(l==i)-int(l==j)) for l in range(r))
        assert canonical(distinct) in rows
    text=f'{r} {K} {len(rows)}\n'+''.join(' '.join(map(str,row))+'\n' for row in rows)
    assert record['input_sha256']==sha(text.encode())
    assert (OUT/record['input_file']).read_text()==text
    return rows,text


def check_witnesses(c,record,rows):
    full=load(record['case']+'.json')
    assert full['rows']==[list(row) for row in rows]
    assert len(full['witnesses'])==len(rows)
    var_at=dict(zip(record['T'],record['point_variables']))
    for row,w in zip(rows,full['witnesses']):
        left,right=w['left'],w['right']
        assert len(left)==len(right)==3 and left==sorted(left) and right==sorted(right) and left!=right
        assert all(s in var_at for s in left+right)
        assert sum(left) % V==sum(right) % V==w['base_sum']
        actual=[0]*len(row)
        for s in left:
            actual[var_at[s]]+=1
        for s in right:
            actual[var_at[s]]-=1
        assert tuple(actual)==row


def check_tree(record,text):
    raw=gzip.decompress((OUT/record['proof']).read_bytes())
    assert sha(raw)==record['proof_sha256_uncompressed'] and len(raw)==record['proof_bytes_uncompressed']
    with tempfile.TemporaryDirectory(prefix=PREFIX) as td:
        inp=Path(td)/(PREFIX+'independent.rows')
        proof=Path(td)/(PREFIX+'proof.tree')
        inp.write_text(text)
        proof.write_bytes(raw)
        checked=json.loads(subprocess.check_output([str(CHECKER),str(inp),str(proof)]))
    assert all(checked[key]==record[key] for key in checked)
    r=int(text.split()[0])
    assert checked['covered_assignments']==13**(r-1)==record['normalized_assignments']
    return checked


def check_sat(record,rows):
    tags,T=record['tags'],record['T']
    assert len(tags)==record['variable_count'] and tags[0]==0 and all(0<=x<K for x in tags)
    assert all(sum(a*b for a,b in zip(row,tags)) % K != 0 for row in rows)
    cs=[tags[i] for i in record['point_variables']]
    # Other CRT formula than the generator's, followed by all multiset triples.
    A=[c+K*((s-c)*pow(K,-1,V) % V) for s,c in zip(T,cs)]
    assert all(0<=a<M and a % V==s and a % K==c for a,s,c in zip(A,T,cs))
    assert len(set(A))==len(A)==len(set(T))
    triples=set()
    for i in range(len(A)):
        for j in range(i,len(A)):
            for l in range(j,len(A)):
                x=(A[i]+A[j]+A[l]) % M
                assert x not in triples
                triples.add(x)
    pairs=[(A[i]+A[j]) % M for i in range(len(A)) for j in range(i,len(A))]
    assert len(pairs)==len(set(pairs))
    assert {Q*x % M for x in A}==set(A)
    assert record['verification']=={'CRT_A_in_T_order':A,'point_tags_in_T_order':cs,
        'distinct_parameters':len(T),'distinct_triple_sums':len(triples),
        'strong_B3':True,'actual_cyclic_frobenius_invariant':True}
    return {'n':len(A),'distinct_triples':len(triples),'distinct_pairs':len(pairs)}


def check_baseline():
    baseline=json.loads((HERE/(PREFIX+'baseline.json')).read_text())
    # Paths in the snapshot are relative to /workspace/leanproject.
    for relative,h in baseline.items():
        assert sha((HERE.parent/relative).read_bytes())==h, ('existing file modified',relative)
    return {'existing_files_unchanged':len(baseline)}


def check_clique(record,rows,certificate):
    assert certificate['status']=='PIGEONHOLE_CERTIFICATE'
    forms=certificate['forms']
    r=record['variable_count']
    assert len(forms)==14 and len({tuple(f) for f in forms})==14
    assert all(len(f)==r and sum(f)==0 for f in forms)
    pairs=certificate['pairs']
    expected={(i,j) for i in range(14) for j in range(i+1,14)}
    assert len(pairs)==len(expected) and {(p['i'],p['j']) for p in pairs}==expected
    for p in pairs:
        i,j=p['i'],p['j']
        scalar=p['scalar_mod_13']
        assert 1<=scalar<13
        row=rows[p['row_id']]
        assert all((a-b-scalar*x) % 13==0 for a,b,x in zip(forms[i],forms[j],row))
    assert certificate['core_constraint_ids']==sorted({p['row_id'] for p in pairs})
    assert len(forms)>13
    return len(certificate['core_constraint_ids'])


def check_negation(record,rows,certificate):
    assert certificate['status']=='NEGATION_ORBIT_CERTIFICATE'
    forms=certificate['forms']
    r=record['variable_count']
    assert len(forms)==7 and len({tuple(f) for f in forms})==7
    assert all(len(f)==r and sorted(f)==[-1]+[0]*(r-2)+[1] for f in forms)
    identities=certificate['identities']
    expected={(i,None,0) for i in range(7)} | {(i,j,s) for i in range(7) for j in range(i+1,7) for s in (-1,1)}
    assert len(identities)==49 and {(t['i'],t['j'],t['sign']) for t in identities}==expected
    for t in identities:
        i,j,s=t['i'],t['j'],t['sign']
        scalar=t['scalar_mod_13']
        assert 1<=scalar<13
        row=rows[t['row_id']]
        left=forms[i] if j is None else [a+s*b for a,b in zip(forms[i],forms[j])]
        assert all((x-scalar*y) % 13==0 for x,y in zip(left,row))
    assert certificate['core_constraint_ids']==sorted({t['row_id'] for t in identities})
    nonzero_orbits={tuple(sorted({x,-x % 13})) for x in range(1,13)}
    assert nonzero_orbits=={(j,13-j) for j in range(1,7)} and len(nonzero_orbits)<len(forms)
    return len(certificate['core_constraint_ids'])


def check_bad_trees(record,text):
    """Negative controls: no new search; reject incomplete/false refutations."""
    raw=gzip.decompress((OUT/record['proof']).read_bytes()).decode()
    lines=raw.splitlines()
    variants={'truncated': '\n'.join(lines[:-1])+'\n',
              'surplus':raw+'-1\n',
              'false_root_conflict':lines[0]+'\n-1\n'}
    rejected=[]
    with tempfile.TemporaryDirectory(prefix=PREFIX) as td:
        inp=Path(td)/(PREFIX+'negative.rows')
        proof=Path(td)/(PREFIX+'negative.tree')
        inp.write_text(text)
        for name,body in variants.items():
            proof.write_text(body)
            run=subprocess.run([str(CHECKER),str(inp),str(proof)],capture_output=True,text=True)
            assert run.returncode != 0 and 'INVALID CERTIFICATE:' in run.stderr
            rejected.append(name)
    return rejected


def check_sat_controls(c):
    """Fixed test vectors, not searches and not extra claimed deletion results."""
    T=c['orbits'][0]['points']
    A=[s+V*((-s)*pow(V,-1,K) % K) for s in T]
    record={'T':T,'tags':[0],'variable_count':1,'point_variables':[0,0,0],
            'verification':{'CRT_A_in_T_order':A,'point_tags_in_T_order':[0,0,0],
                'distinct_parameters':3,'distinct_triple_sums':10,'strong_B3':True,
                'actual_cyclic_frobenius_invariant':True}}
    positive=check_sat(record,[])
    # Three distinct parameters with no two different all-distinct triples, but
    # the repeated triples (0,0,2) and (0,1,1) collide. Must be rejected.
    bad={'T':[0,1,2],'tags':[0,1,2],'variable_count':3,'point_variables':[0,1,2]}
    try:
        check_sat(bad,[])
    except AssertionError:
        rejected=True
    else:
        raise AssertionError('Repeated-triple control was not rejected')
    return {'fixed_three_point_orbit_positive_control':positive,
            'repeated_triple_collision_control_rejected':rejected,
            'scope':'verifier regression only, not a searched deletion case'}


def main():
    global OUT
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--construction-only',action='store_true')
    parser.add_argument('--out',type=Path,default=OUT,help='audit result directory')
    args=parser.parse_args()
    OUT=args.out.resolve()
    c=load('construction.json')
    summary={'construction':check_construction(c),'baseline':check_baseline()}
    if not args.construction_only:
        subprocess.run(['g++','-O3','-std=c++17','-Wall','-Wextra','-pedantic',
                        str(HERE/(PREFIX+'verify_tree.cpp')),'-o',str(CHECKER)],check=True)
        data=load('results.json')
        expected=[(d,keep) for m,keep in [(1,True),(1,False),(2,True),(2,False)]
                  for d in itertools.combinations(range(9),m)]
        records=data['instances']
        assert [(tuple(r['deleted_orbits']),r['keep_infinity']) for r in records]==expected
        clique_data=load('cliques.json')
        negation_data=load('negation.json')
        case_set={r['case'] for r in records}
        assert {x['case'] for x in clique_data}==case_set and len(clique_data)==len(case_set)
        assert {x['case'] for x in negation_data}==case_set and len(negation_data)==len(case_set)
        cliques={x['case']:x['attempts'][-1] for x in clique_data}
        negation={x['case']:x['certificate'] for x in negation_data}
        total_nodes=0
        sat=[]
        clique_sizes=[]
        negation_sizes=[]
        for record in records:
            rows,text=reconstruct(c,record)
            check_witnesses(c,record,rows)
            if record['status']=='UNSAT':
                checked=check_tree(record,text)
                total_nodes+=checked['nodes']
            elif record['status']=='SAT':
                sat.append(check_sat(record,rows))
            else:
                assert record['status'] in ('TIMEOUT','UNATTEMPTED_BUDGET')
            clique_sizes.append(check_clique(record,rows,cliques[record['case']]))
            negation_sizes.append(check_negation(record,rows,negation[record['case']]))
        first=records[0]
        rows,text=reconstruct(c,first)
        negative_controls=check_bad_trees(first,text)
        sat_controls=check_sat_controls(c)
        example=load('example_core.json')
        source=load(example['case']+'.json')
        assert example['case']=='n21_d4_5' and example['certificate']==negation[example['case']]
        assert example['n']==source['n']==21 and example['keep_infinity'] is False
        assert example['deleted_orbits']==source['deleted_orbits']==[4,5]
        assert example['variables']==source['variables']
        ids=example['certificate']['core_constraint_ids']
        assert len(ids)==34
        assert example['core']==[{'row_id':j,'row':source['rows'][j],'witness':source['witnesses'][j]} for j in ids]
        by_n={str(n):dict(Counter(r['status'] for r in records if r['n']==n)) for n in [25,24,22,21]}
        assert by_n==data['summary']['by_n']
        ledger=load('search_ledger.json')
        elapsed=sum(x['process_wall_seconds'] for x in ledger['charges'])
        assert elapsed<=ledger['cap_seconds']==300.0
        assert len({x['case'] for x in ledger['charges']})==len(ledger['charges'])
        by_case={x['case']:x for x in ledger['charges']}
        for r in records:
            if r['status']!='UNATTEMPTED_BUDGET':
                charge=by_case[r['case']]
                assert charge['status']==r['status'] and charge['process_wall_seconds']==r['process_wall_seconds']
        solver_wall=sum(r.get('process_wall_seconds',0) for r in records)
        dfs_seconds=sum(r.get('elapsed_ms',0) for r in records)/1000
        assert solver_wall==data['summary']['search_process_wall_seconds']
        assert dfs_seconds==data['summary']['dfs_seconds']
        summary.update({'cases_checked':len(records),'by_n':by_n,'tree_nodes_checked':total_nodes,
                        'SAT_direct_checks':sat,'search_process_wall_seconds':elapsed,
                        'solver_process_wall_seconds':solver_wall,'solver_DFS_seconds':dfs_seconds,
                        'search_cap_seconds':ledger['cap_seconds'],
                        'pigeonhole_certificates_checked':len(clique_sizes),
                        'pigeonhole_core_size_range':[min(clique_sizes),max(clique_sizes)],
                        'negation_orbit_certificates_checked':len(negation_sizes),
                        'negation_core_size_range':[min(negation_sizes),max(negation_sizes)],
                        'negation_identities_checked':49*len(negation_sizes),
                        'nonzero_negation_orbits_mod_13':[[j,13-j] for j in range(1,7)],
                        'bad_tree_controls_rejected':negative_controls,
                        'SAT_checker_controls':sat_controls,
                        'example_core_original_inequalities_checked':len(ids),
                        'invariant_retention_upper_bound_by_heredity':19,
                        'upper_bound_attainment':'not tested',
                        'cube_root_M':M**(1/3)})
    summary['status']='PASS'
    path('verification.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2))


if __name__=='__main__':
    main()
