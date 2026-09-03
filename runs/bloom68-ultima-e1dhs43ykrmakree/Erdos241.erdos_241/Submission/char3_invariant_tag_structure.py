#!/usr/bin/env python3
"""Extract small/global certificates from the exact orbit-variable audit.
All NEW certificate searches are charged to the same 300-second ledger.
"""
from __future__ import annotations
import argparse
import itertools as it
import json
from pathlib import Path
import time

import char3_invariant_tag_audit as audit
from char3_invariant_tag_audit import Budget, OUT, K, data_path, write_json


def projective(row):
    row=tuple(a % K for a in row)
    leading=next((a for a in row if a),None)
    if leading is None:
        return row
    inv=pow(leading,-1,K)
    return tuple(a*inv % K for a in row)


def clique_at_least(adj,target,deadline):
    calls=0
    def rec(chosen,available):
        nonlocal calls
        calls+=1
        if calls % 1024==0 and time.monotonic()>deadline:
            raise TimeoutError
        if len(chosen)>=target:
            return chosen
        if len(chosen)+available.bit_count()<target:
            return None
        # Greedy coloring bounds the maximum clique in the candidate graph.
        remaining=available
        order,bounds=[],[]
        color=0
        while remaining:
            color+=1
            same=remaining
            while same:
                bit=same & -same
                v=bit.bit_length()-1
                remaining^=bit
                same^=bit
                same &= ~adj[v]
                order.append(v)
                bounds.append(color)
        for v,bound in reversed(list(zip(order,bounds))):
            if len(chosen)+bound<target:
                return None
            result=rec(chosen+[v],available & adj[v])
            if result is not None:
                return result
            available &= ~(1<<v)
        return None
    result=rec([], (1<<len(adj))-1)
    return result,calls


def make_clique(instance,kind,deadline):
    r=instance['variable_count']
    row_map={projective(row):j for j,row in enumerate(instance['rows'])}
    if kind=='differences':
        forms=[(0,)*r]+[tuple(int(l==i)-int(l==j) for l in range(r))
                          for i in range(r) for j in range(r) if i!=j]
    elif kind=='pair_sums':
        forms=[tuple(int(l==i)+int(l==j) for l in range(r))
               for i in range(r) for j in range(i,r)]
    else:
        raise ValueError(kind)
    adj=[0]*len(forms)
    for i,j in it.combinations(range(len(forms)),2):
        delta=projective(tuple(x-y for x,y in zip(forms[i],forms[j])))
        if delta in row_map:
            adj[i] |= 1<<j
            adj[j] |= 1<<i
    chosen,calls=clique_at_least(adj,14,deadline)
    if chosen is None:
        return {'status':'NO_14_CLIQUE_IN_SELECTED_FORMS','kind':kind,'calls':calls}
    chosen_forms=[forms[i] for i in sorted(chosen)]
    pairs=[]
    for i,j in it.combinations(range(14),2):
        delta=tuple(x-y for x,y in zip(chosen_forms[i],chosen_forms[j]))
        row_id=row_map[projective(delta)]
        row=instance['rows'][row_id]
        l=next(l for l,a in enumerate(row) if a % K)
        scalar=delta[l]*pow(row[l] % K,-1,K) % K
        assert scalar and all((x-scalar*y) % K==0 for x,y in zip(delta,row))
        pairs.append({'i':i,'j':j,'row_id':row_id,'scalar_mod_13':scalar})
    return {'status':'PIGEONHOLE_CERTIFICATE','kind':kind,'calls':calls,
            'forms':chosen_forms,'pairs':pairs,
            'core_constraint_ids':sorted({p['row_id'] for p in pairs})}


def make_negation(instance,deadline):
    """Seven nonzero expressions in distinct +/- orbits cannot fit F13*."""
    r=instance['variable_count']
    row_map={projective(row):j for j,row in enumerate(instance['rows'])}
    forms=[tuple(int(l==i)-int(l==j) for l in range(r)) for i,j in it.combinations(range(r),2)]
    def available(row):
        return projective(row) in row_map
    assert all(available(form) for form in forms)
    adj=[0]*len(forms)
    for i,j in it.combinations(range(len(forms)),2):
        if all(available(tuple(x+sign*y for x,y in zip(forms[i],forms[j]))) for sign in [-1,1]):
            adj[i] |= 1<<j
            adj[j] |= 1<<i
    chosen,calls=clique_at_least(adj,7,deadline)
    if chosen is None:
        return {'status':'NO_7_NEGATION_CLIQUE_IN_SELECTED_FORMS','calls':calls}
    chosen_forms=[forms[i] for i in sorted(chosen)]
    identities=[]
    for i in range(7):
        for j,sign in [(None,0)]+[(j,sign) for j in range(i+1,7) for sign in [-1,1]]:
            delta=chosen_forms[i] if j is None else tuple(x+sign*y for x,y in zip(chosen_forms[i],chosen_forms[j]))
            row_id=row_map[projective(delta)]
            row=instance['rows'][row_id]
            l=next(l for l,a in enumerate(row) if a % K)
            scalar=delta[l]*pow(row[l] % K,-1,K) % K
            assert scalar and all((x-scalar*y) % K==0 for x,y in zip(delta,row))
            identities.append({'i':i,'j':j,'sign':sign,'row_id':row_id,'scalar_mod_13':scalar})
    assert len(identities)==49
    return {'status':'NEGATION_ORBIT_CERTIFICATE','calls':calls,'forms':chosen_forms,
            'identities':identities,'core_constraint_ids':sorted({t['row_id'] for t in identities})}


def negation():
    budget=Budget()
    cases=json.loads(data_path('instances.json').read_text())
    cases.sort(key=lambda x:(x['n'],x['case']))
    results=[]
    for record in cases:
        instance=json.loads(data_path(record['case']+'.json').read_text())
        if 300-budget.used<1:
            break
        start=time.monotonic()
        try:
            cert=make_negation(instance,start+1.0)
        except TimeoutError:
            cert={'status':'TIMEOUT'}
        elapsed=time.monotonic()-start
        budget.data['charges'].append({'case':record['case']+'_negation','status':cert['status'],
            'limit_seconds':1.0,'process_wall_seconds':elapsed,
            'accounting_kind':'in-process structural certificate search'})
        write_json(budget.path,budget.data)
        results.append({'case':record['case'],'certificate':cert})
        write_json(data_path('negation.json'),results)
        print(record['case'],cert['status'],len(cert.get('core_constraint_ids',[])),'rows',flush=True)
    print('Total search budget charged:',budget.used,flush=True)


def cliques():
    budget=Budget()
    cases=json.loads(data_path('instances.json').read_text())
    # First try the weakest (n=21) cases; larger-case certificates are optional.
    cases.sort(key=lambda x:(x['n'],x['case']))
    results=[]
    for record in cases:
        instance=json.loads(data_path(record['case']+'.json').read_text())
        entry={'case':record['case'],'attempts':[]}
        for kind in ['differences','pair_sums']:
            left=300-budget.used
            if left<1:
                break
            limit=min(1.0,left-0.1)
            start=time.monotonic()
            try:
                ans=make_clique(instance,kind,start+limit)
            except TimeoutError:
                ans={'status':'TIMEOUT','kind':kind}
            elapsed=time.monotonic()-start
            name=record['case']+'_clique_'+kind
            budget.data['charges'].append({'case':name,'status':ans['status'],
                'limit_seconds':limit,'process_wall_seconds':elapsed,
                'accounting_kind':'in-process structural certificate search'})
            write_json(budget.path,budget.data)
            entry['attempts'].append(ans)
            if ans['status']=='PIGEONHOLE_CERTIFICATE':
                break
        results.append(entry)
        write_json(data_path('cliques.json'),results)
        if entry['attempts'] and entry['attempts'][-1]['status']=='PIGEONHOLE_CERTIFICATE':
            cert=entry['attempts'][-1]
            print(record['case'],cert['kind'],len(cert['core_constraint_ids']),'rows',flush=True)
        else:
            print(record['case'],'no simple clique found',flush=True)
    print('Total search budget charged:',budget.used,flush=True)


def example():
    """Materialize the 34-row example; this is formatting, not another search."""
    name='n21_d4_5'
    instance=json.loads(data_path(name+'.json').read_text())
    cert=next(x['certificate'] for x in json.loads(data_path('negation.json').read_text()) if x['case']==name)
    ids=cert['core_constraint_ids']
    assert cert['status']=='NEGATION_ORBIT_CERTIFICATE' and len(ids)==34
    out={'case':name,'variables':instance['variables'],'deleted_orbits':instance['deleted_orbits'],
         'keep_infinity':False,'n':21,'certificate':cert,
         'core':[{'row_id':j,'row':instance['rows'][j],'witness':instance['witnesses'][j]} for j in ids],
         'minimality':'not asserted; 34 original inequalities suffice by the seven-form negation argument'}
    write_json(data_path('example_core.json'),out)
    lines=['# A 34-row exact certificate at q=27','',
           'Delete infinity and orbits 4 and 5. Labels `c_j` denote full-orbit labels, not individual point labels.',
           'Variables in row order: '+str(instance['variables'])+'.','',
           'Define `L1,...,L7 = c1-c2, c2-c3, c2-c7, c2-c8, c3-c7, c3-c8, c7-c8`.',
           'The identities below force every Li and every Li +/- Lj to be nonzero modulo 13.',
           'Thus seven Li must occupy distinct nonzero negation orbits, but F13 has only six. Contradiction.',
           'No tag normalization, UNSAT flag, or exhaustive tree is needed for this argument.',
           'This is a sufficient core; no minimum or inclusion-minimal claim is made.','',
           '## The original multiset-triple inequalities','',
           '`Rj` is the indicated left tag sum minus right tag sum, using constant tags on each full orbit.',
           'Every equality in the table is modulo 757; coherence requires `Rj != 0 mod 13`.',
           'Repeated entries are intentional. All point entries are retained Singer bases.','',
           '| Row | Left base triple | Right base triple | Common base sum |',
           '|---:|---|---|---:|']
    for j in ids:
        w=instance['witnesses'][j]
        lines.append(f"| {j} | {tuple(w['left'])} | {tuple(w['right'])} | {w['base_sum']} |")
    def expression(t):
        scalar=t['scalar_mod_13']
        scalar=scalar if scalar<=6 else scalar-13
        lead='' if scalar==1 else '-' if scalar==-1 else str(scalar)+' '
        return lead+'R'+str(t['row_id'])
    identities={(t['i'],t['j'],t['sign']):t for t in cert['identities']}
    lines += ['','## Identities over F13','',
              'Coefficients are reduced modulo 13 (in particular, `3^(-1)=9=-4`).','',
              '| Form | Equal row expression |','|---|---|']
    for i in range(7):
        lines.append(f'| L{i+1} | {expression(identities[i,None,0])} |')
    lines += ['','| Pair | Li - Lj | Li + Lj |','|---|---|---|']
    for i,j in it.combinations(range(7),2):
        lines.append(f'| {i+1}, {j+1} | {expression(identities[i,j,-1])} | {expression(identities[i,j,1])} |')
    lines += ['','The last six forms are all six differences of the four tags `c2,c3,c7,c8`.',
              'Their +/- values would already exhaust F13*, and the extra nonzero `c1-c2` is forbidden from all of them.',
              'All 49 identities and all source triples are independently checked by `char3_invariant_tag_verify.py`.','']
    data_path('example_certificate.md').write_text('\n'.join(lines))
    print('Exported the 34-row example certificate (no new search).')


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command',choices=['cliques','negation','example'])
    parser.add_argument('--out',type=Path,default=OUT,help='audit result directory')
    args=parser.parse_args()
    audit.OUT=args.out.resolve()
    if data_path(args.command+'.json').exists():
        raise SystemExit('Refusing to overwrite certificate searches; use a fresh --out directory for replay.')
    if args.command=='cliques':
        cliques()
    elif args.command=='negation':
        negation()
    else:
        example()


if __name__=='__main__':
    main()
