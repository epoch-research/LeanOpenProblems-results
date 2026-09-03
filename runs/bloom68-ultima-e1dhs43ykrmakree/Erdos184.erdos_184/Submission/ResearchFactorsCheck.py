"""Targeted exact checks for ResearchFactors; no optimization claims inferred from samples."""
from collections import Counter, defaultdict, deque
from itertools import combinations
from fractions import Fraction
from pathlib import Path
import hashlib, json, random
import networkx as nx

SPEC = Path(__file__).resolve().with_name('Spec.lean')
SPEC_HASH = '429c12b5b471b0098bbc8ded194d7c22a4b99c083841d9a549f2bc3cc87dafde'

def check_spec():
    assert hashlib.sha256(SPEC.read_bytes()).hexdigest() == SPEC_HASH

def ce(u,v): return tuple(sorted((u,v)))
def edges_of(C): return [ce(u,v) for u,v in zip(C,C[1:]+C[:1])]

def check_simple_factors(G,F,full=True):
    E=Counter()
    for factor in F:
        used=set()
        for C in factor:
            assert len(C)>=3 and len(set(C))==len(C)
            assert not (set(C)&used)
            used.update(C); E.update(edges_of(C))
        if full: assert used==set(G)
    assert E==Counter({ce(u,v):1 for u,v in G.edges})

# Each record has an immutable ID, endpoints, and kind: real / virtual.
def partial_factors(nodes, records, r):
    H=nx.MultiGraph(); H.add_nodes_from(nodes)
    for eid,(u,v,kind) in records.items(): H.add_edge(u,v,key=eid)
    assert all(d%2==0 and d<=2*r for v,d in H.degree)
    arcs=[]
    for S in nx.connected_components(H):
        K=H.subgraph(S).copy()
        if K.number_of_edges():
            for u,v,eid in nx.eulerian_circuit(K,keys=True): arcs.append((u,v,eid))
    holes={v:r-H.degree(v)//2 for v in H}
    for v,h in holes.items():
        for j in range(h): arcs.append((v,v,('dummy',v,j)))
    queues=defaultdict(list)
    B=nx.Graph(); left=[(0,v) for v in nodes]; right=[(1,v) for v in nodes]
    B.add_nodes_from(left,bipartite=0); B.add_nodes_from(right,bipartite=1)
    for u,v,eid in arcs:
        queues[(u,v)].append(eid); B.add_edge((0,u),(1,v))
    result=[]; covered=Counter(); missing=Counter()
    for color in range(r):
        M=nx.algorithms.bipartite.hopcroft_karp_matching(B,top_nodes=left)
        assert all(x in M for x in left)
        successor={u:M[(0,u)][1] for u in nodes}; labels={}
        assert len(set(successor.values()))==len(nodes)
        for u,v in successor.items():
            labels[u]=queues[(u,v)].pop()
            if not queues[(u,v)]: B.remove_edge((0,u),(1,v))
        seen=set(); cycles=[]
        for v in nodes:
            if v in seen: continue
            C=[]; ids=[]; w=v
            while w not in seen:
                seen.add(w); C.append(w); ids.append(labels[w]); w=successor[w]
            assert w==v
            if len(C)==1:
                assert ids[0][0]=='dummy' and ids[0][1]==v
                missing[v]+=1
            else:
                assert len(set(C))==len(C)
                assert all(eid in records for eid in ids)
                for a,b,eid in zip(C,C[1:]+C[:1],ids):
                    assert ce(a,b)==ce(*records[eid][:2])
                covered.update(ids); cycles.append((tuple(C),tuple(ids)))
        result.append(cycles)
    assert B.number_of_edges()==0
    assert covered==Counter({eid:1 for eid in records})
    assert dict(missing)=={v:h for v,h in holes.items() if h}
    return result,holes

def simple_partial_factors(G,r):
    records={('e',u,v):(u,v,'real') for u,v in G.edges}
    F,_=partial_factors(sorted(G),records,r)
    F=[[C for C,ids in factor] for factor in F]
    check_simple_factors(G,F,False)
    return F

def walecki(r):
    d=2*r; inf=d; cycles=[]
    for i in range(r):
        C=[inf,i]
        for j in range(1,r): C.extend(((i-j)%d,(i+j)%d))
        C.append((i-r)%d); cycles.append(tuple(C))
    K=nx.complete_graph(d+1)
    check_simple_factors(K,[[C] for C in cycles])
    matching={}
    for x in range(r):
        e=ce(x,x+r); colors=[i for i,C in enumerate(cycles) if e in edges_of(C)]
        assert colors==[(x+(r+1)//2)%r]
        matching[colors[0]]=e
    assert len(matching)==r and len(set(v for e in matching.values() for v in e))==d
    return cycles,matching

def regular_completion(H,r):
    assert set(H)==set(range(len(H))) and all(d%2==0 and d<=2*r for v,d in H.degree)
    N=len(H); d=2*r; C,M=walecki(r)
    F=simple_partial_factors(H,r)
    G=H.copy(); local=[]
    used={v:{i for i,ff in enumerate(F) if any(v in cyc for cyc in ff)} for v in H}
    deficient=[v for v in H if H.degree(v)<d]
    for v in deficient:
        k=H.degree(v)//2
        perm=sorted(used[v])+[i for i in range(r) if i not in used[v]]
        label=lambda x:N+v*(d+1)+x
        lobe=[]
        for i,cycle in enumerate(C):
            cyc=[]
            for a,b in zip(cycle,cycle[1:]+cycle[:1]):
                cyc.append(label(a))
                if i>=k and ce(a,b)==M[i]: cyc.append(v)
            cyc=tuple(cyc); F[perm[i]].append(cyc); lobe.append(cyc)
            for a,b in edges_of(cyc):
                assert not G.has_edge(a,b); G.add_edge(a,b)
        local.append(lobe)
    assert len(G)==N+(d+1)*len(deficient) and all(deg==d for v,deg in G.degree)
    check_simple_factors(G,F)
    assert sum(map(len,F))==r*len(deficient)+sum(map(len,simple_partial_factors(H,r)))
    return G,F,local

def block_ledger(G):
    d=next(iter(dict(G.degree).values()))
    assert all(x==d for v,x in G.degree) and d%2==0
    blocks=[G.subgraph(S).copy() for S in nx.biconnected_components(G)]
    c=nx.number_connected_components(G); n=len(G); b=len(blocks)
    assert all(len(H)>=3 for H in blocks)
    assert sum(len(H)-1 for H in blocks)==n-c
    deficiency=sum(d-H.degree(v) for H in blocks for v in H)
    assert deficiency==d*(b-c)
    assert 2*d*b<=3*n-(d+3)*c
    assert Fraction(deficiency,2)<=Fraction(3,4)*(n-(d+1)*c)
    return dict(n=n,d=d,blocks=b,holes=deficiency//2)

# Recursively split along two vertices. Both children get the poles, but each
# old edge belongs to exactly one child. Add a PAIR of virtual edges only if
# each child is odd at both poles.
def separator_decomposition(G):
    original_n=len(G); d=next(iter(dict(G.degree).values()))
    initial={('real',u,v):(u,v,'real') for u,v in G.edges}
    serial=[0]; leaves=[]; parity_splits=[0]
    def split(nodes,records):
        H=nx.Graph(); H.add_nodes_from(nodes); H.add_edges_from((u,v) for u,v,k in records.values())
        if len(nodes)==3:
            leaves.append((nodes,records)); return ('leaf',len(leaves)-1)
        sep=None
        for u,v in combinations(sorted(nodes),2):
            comps=list(nx.connected_components(H.subgraph(set(nodes)-{u,v})))
            if len(comps)>1:
                A=set(comps[0]); B=set(nodes)-{u,v}-A
                sep=(u,v,A,B); break
        if sep is None:
            assert nx.node_connectivity(H)>=3
            leaves.append((nodes,records)); return ('leaf',len(leaves)-1)
        u,v,A,B=sep; S={u,v}; R1={};R2={}
        for eid,rec in records.items():
            a,b,kind=rec
            if a in A or b in A: R1[eid]=rec
            elif a in B or b in B: R2[eid]=rec
            else: R1[eid]=rec
        deg1=Counter(w for rec in R1.values() for w in rec[:2])
        deg2=Counter(w for rec in R2.values() for w in rec[:2])
        assert deg1[u]%2==deg1[v]%2==deg2[u]%2==deg2[v]%2
        pair=None
        if deg1[u]%2:
            sid=serial[0]; serial[0]+=1; parity_splits[0]+=1
            e1=('virtual',sid,0);e2=('virtual',sid,1)
            R1[e1]=(u,v,'virtual');R2[e2]=(u,v,'virtual');pair=(e1,e2)
        for V,R in [(A|S,R1),(B|S,R2)]:
            deg=Counter(w for rec in R.values() for w in rec[:2])
            assert len(V)>=3 and all(deg[w]%2==0 and deg[w]<=d for w in V)
        return ('split',split(A|S,R1),split(B|S,R2),pair)
    tree=split(set(G),initial); t=len(leaves); P=parity_splits[0]
    assert sum(len(V)-2 for V,R in leaves)==original_n-2
    assert sum(sum(rec[2]=='real' for rec in R.values()) for V,R in leaves)==G.number_of_edges()
    assert sum(sum(rec[2]=='virtual' for rec in R.values()) for V,R in leaves)==2*P
    real_def=sum(d*len(V)-2*sum(rec[2]=='real' for rec in R.values()) for V,R in leaves)
    aug_def=sum(d*len(V)-2*len(R) for V,R in leaves)
    assert real_def==2*d*(t-1) and aug_def==2*d*(t-1)-4*P
    if d>3:
        assert (d-3)*t<=3*original_n-2*d-6
    return leaves,tree,dict(n=original_n,d=d,pieces=t,parity_splits=P,virtual_edges=2*P,holes=aug_def//2)

def glue_leaf_cycles(G,leaves,tree):
    d=next(iter(dict(G.degree).values())); r=d//2; all_records={}
    DC=[]
    for V,R in leaves:
        all_records.update(R)
        F,holes=partial_factors(sorted(V),R,r)
        DC.append([ids for factor in F for C,ids in factor])
    def glue(T):
        if T[0]=='leaf': return list(DC[T[1]])
        _,left,right,pair=T; A=glue(left);B=glue(right)
        if pair is None:return A+B
        e1,e2=pair
        x=next(C for C in A if e1 in C); y=next(C for C in B if e2 in C)
        A.remove(x);B.remove(y)
        z=tuple(e for e in x if e!=e1)+tuple(e for e in y if e!=e2)
        # Check simple cycle by its edge set, allowing temporary parallel edges.
        H=nx.MultiGraph()
        for eid in z:
            u,v,kind=all_records[eid];H.add_edge(u,v,key=eid)
        assert nx.is_connected(H) and all(deg==2 for v,deg in H.degree)
        assert len(z)>=2
        return A+B+[z]
    result=glue(tree)
    assert Counter(eid for C in result for eid in C)==Counter({('real',u,v):1 for u,v in G.edges})
    for C in result:
        H=nx.Graph(); H.add_edges_from(all_records[eid][:2] for eid in C)
        assert len(C)==len(H)>=3 and nx.is_connected(H) and all(x==2 for v,x in H.degree)
    return len(result),sum(map(len,DC))

# A supplied factorization of each side of a 2-vertex cut need not be
# compatible under whole-side color permutations.
def profile_example():
    u,v=0,1
    L=[(u,2,4,v,3,5),(2,3,4,5)]
    R=[(u,6,7,8,9),(v,8,6,9,7)]
    G=nx.Graph()
    for C in L+R:G.add_edges_from(edges_of(C))
    assert len(G)==10 and all(d==4 for x,d in G.degree)
    assert set(L[0])&{u,v}=={u,v} and not (set(L[1])&{u,v})
    assert set(R[0])&{u,v}=={u} and set(R[1])&{u,v}=={v}
    for perm in [(0,1),(1,0)]:
        assert any(len([C for C in [L[i],R[perm[i]]] if x in C])!=1 for i in [0,1] for x in [u,v])
    # Exact Hamilton decomposition witness, not a minimum-search heuristic.
    witness=None
    def dfs(P):
        nonlocal witness
        if witness:return
        if len(P)==len(G):
            if not G.has_edge(P[-1],P[0]):return
            H=G.copy();H.remove_edges_from(edges_of(tuple(P)))
            if nx.is_connected(H):
                Q=tuple(nx.find_cycle(H)[i][0] for i in range(len(H)))
                witness=[tuple(P),Q]
            return
        for w in sorted(G[P[-1]]):
            if w not in P:dfs(P+[w])
    dfs([0]); assert witness
    check_simple_factors(G,[[C] for C in witness])
    return dict(n=10,old_cycles=[list(C) for C in L+R],hamilton_cycles=[list(C) for C in witness])

def cayley_factorization_check():
    ps=[]
    for i in range(3):
     p=list(range(7));p[0]=2*i+1;p[2*i+1]=2*i+2;p[2*i+2]=0;ps.append(tuple(p))
    def mul(g,p):return tuple(p[z] for z in g)
    S=ps+[mul(p,p) for p in ps];identity=tuple(range(7))
    group=[identity];ix={identity:0};Q=deque(group)
    while Q:
     g=Q.popleft()
     for s in S:
      h=mul(g,s)
      if h not in ix:ix[h]=len(group);group.append(h);Q.append(h)
    assert len(group)==2520
    G=nx.Graph();G.add_nodes_from(range(len(group)))
    T=set()
    for g in group:
     for p in ps:
      gp=mul(g,p);gpp=mul(gp,p);T.add(tuple(sorted((ix[g],ix[gp],ix[gpp]))))
    T=sorted(T)
    for C in T:G.add_edges_from(combinations(C,2))
    assert len(T)==2520 and G.number_of_edges()==7560
    assert all(d==6 for v,d in G.degree)
    assert Counter(ce(u,v) for C in T for u,v in combinations(C,2))==Counter({ce(u,v):1 for u,v in G.edges})
    I=nx.Graph();left=[('t',j) for j in range(len(T))];right=[('v',v) for v in G]
    I.add_nodes_from(left,bipartite=0);I.add_nodes_from(right,bipartite=1)
    for j,C in enumerate(T):I.add_edges_from((('t',j),('v',v)) for v in C)
    
    distance={('v',0):0};parent={('v',0):None};queue=deque([('v',0)]);girth=10**9
    while queue:
     u=queue.popleft()
     for v in I[u]:
      if v not in distance:
       distance[v]=distance[u]+1;parent[v]=u;queue.append(v)
      elif parent[u]!=v and parent[v]!=u:girth=min(girth,distance[u]+distance[v]+1)
    assert girth==16
    M=nx.algorithms.bipartite.hopcroft_karp_matching(I,top_nodes=left)
    assert all(t in M for t in left)
    F=nx.Graph();F.add_nodes_from(G);middles=[]
    for j,C in enumerate(T):
     middle=M[('t',j)][1];middles.append(middle);a,b=[v for v in C if v!=middle];F.add_edge(a,b)
    assert all(d==2 for v,d in F.degree)
    orientation={}
    for comp in nx.connected_components(F):
     for u,v in nx.eulerian_circuit(F.subgraph(comp).copy()):orientation[frozenset((u,v))]=(u,v)
    DG=nx.DiGraph();DG.add_nodes_from(G)
    for C,middle in zip(T,middles):
     a,b=[v for v in C if v!=middle];u,v=orientation[frozenset((a,b))];DG.add_edges_from([(u,v),(u,middle),(middle,v)])
    assert all(DG.in_degree(v)==DG.out_degree(v)==3 for v in G)
    assert DG.number_of_edges()==G.number_of_edges()
    assert all(int(DG.has_edge(u,v))+int(DG.has_edge(v,u))==1 for u,v in G.edges)
    assert all(nx.is_directed_acyclic_graph(DG.subgraph(C)) for C in T)
    B=nx.Graph();L=[('l',v) for v in DG];R=[('r',v) for v in DG]
    B.add_nodes_from(L,bipartite=0);B.add_nodes_from(R,bipartite=1)
    B.add_edges_from((('l',u),('r',v)) for u,v in DG.edges)
    factors=[]
    for i in range(3):
     match=nx.algorithms.bipartite.hopcroft_karp_matching(B,top_nodes=L)
     p={u:match[('l',u)][1] for u in DG};assert len(set(p.values()))==len(G)
     B.remove_edges_from((('l',u),('r',v)) for u,v in p.items())
     seen=set();cycles=[]
     for u in DG:
      if u in seen:continue
      C=[];v=u
      while v not in seen:seen.add(v);C.append(v);v=p[v]
      assert v==u and len(C)>=8;cycles.append(C)
     assert sum(map(len,cycles))==len(G);factors.append(cycles)
    assert B.number_of_edges()==0
    E=Counter((u,v) for factor in factors for C in factor for u,v in zip(C,C[1:]+C[:1]))
    assert E==Counter({(u,v):1 for u,v in DG.edges})
    check_simple_factors(G,[[tuple(C) for C in ff] for ff in factors])
    report=dict(n=len(G),degree=6,factors=3,components_per_factor=list(map(len,factors)),total_components=sum(map(len,factors)),min_length=min(len(C) for f in factors for C in f),max_length=max(len(C) for f in factors for C in f))
    report['incidence_girth']=girth
    report['cycle_lengths']=[sorted(map(len,ff)) for ff in factors]
    return report


def hole_hall_checks():
    results=[]
    for r,t in [(16,1),(16,3),(20,5),(32,8)]:
        H=nx.Graph();H.add_nodes_from(range(2*t+1))
        for i in range(t):H.add_edges_from(edges_of((2*i,2*i+1,2*i+2)))
        G,F,_=regular_completion(H,r); matched=budget=0
        all_cycles=[C for ff in F for C in ff]
        for S in nx.biconnected_components(G):
            K=G.subgraph(S)
            holes={v:r-K.degree(v)//2 for v in K}
            short=[C for C in all_cycles if set(C)<=S and 8*len(C)<2*r]
            B=nx.Graph();left=[('cycle',i) for i in range(len(short))]
            B.add_nodes_from(left,bipartite=0)
            for i,C in enumerate(short):
                for v in C:
                    B.add_edges_from((('cycle',i),('token',v,j)) for j in range(holes[v]))
            M=nx.algorithms.bipartite.hopcroft_karp_matching(B,top_nodes=left)
            assert all(z in M for z in left)
            matched+=len(short);budget+=sum(holes.values())
        assert matched==t
        results.append(dict(r=r,t=t,n=len(G),matched_short_cycles=matched,hole_tokens=budget))
    return results


def check_deficit_peeling(H,D):
    assert all(d<=D for v,d in H.degree)
    original=H.copy(); K=H.copy(); removed=[]; edges_removed=0
    while True:
        small=[v for v,d in K.degree if 4*d<D]
        if not small:break
        v=min(small);edges_removed+=K.degree(v);removed.append(v);K.remove_node(v)
    R=set(removed)
    deficit_R=sum(D-original.degree(v) for v in R)
    total_deficit=sum(D-d for v,d in original.degree)
    boundary=sum((u in R)!=(v in R) for u,v in original.edges)
    internal=original.subgraph(R).number_of_edges()
    assert edges_removed==internal+boundary
    assert 2*edges_removed<=deficit_R<=total_deficit
    assert D*len(R)<=2*deficit_R
    assert all(4*d>=D for v,d in K.degree)
    return edges_removed


def main():
    check_spec(); report={}; completions=[]
    for r in list(range(2,17))+[20,32]:
        G,F,local=regular_completion(nx.cycle_graph(3),r)
        assert len(G)==6*r+6 and sum(map(len,F))==3*r+1
        assert sum(len(C)==3 for factor in F for C in factor)==1
        assert set(nx.articulation_points(G))=={0,1,2}
        for H in [G.subgraph(set().union(*(set(C) for C in lobe))).copy() for lobe in local]:
            assert nx.is_biconnected(H)
        completions.append(dict(r=r,n=len(G),cycles=sum(map(len,F)),minimum_length=3,ledger=block_ledger(G)))
    report['triangle_completions']=completions
    windmills=[]
    for r in [2,3,4,6,8,12,16,24,32]:
        H=nx.Graph(); H.add_nodes_from(range(2*r+1))
        for i in range(r): H.add_edges_from(edges_of((0,2*i+1,2*i+2)))
        G,F,local=regular_completion(H,r)
        assert len(G)==(2*r+1)**2 and sum(map(len,F))==r*(2*r+1)
        assert all(sum(len(C)==3 for C in ff)==1 for ff in F)
        assert all(len(next(C for C in ff if 0 in C))==3 for ff in F)
        ledger=block_ledger(G)
        assert ledger['blocks']==3*r and ledger['holes']==r*(3*r-1)
        short=[C for ff in F for C in ff if 8*len(C)<2*r]
        B=nx.Graph();left=[('cycle',i) for i in range(len(short))];B.add_nodes_from(left,bipartite=0)
        for i,C in enumerate(short):B.add_edges_from((('cycle',i),('vertex',v)) for v in C)
        M=nx.algorithms.bipartite.hopcroft_karp_matching(B,top_nodes=left)
        assert all(z in M for z in left)
        windmills.append(dict(r=r,n=len(G),cycles=sum(map(len,F)),components_per_factor=[len(ff) for ff in F],ledger=ledger,short_representatives=len(short)))
    report['windmill_completions']=windmills
    chains=[]
    for r,t in [(3,1),(3,3),(4,2),(4,5),(8,3),(12,8),(20,10)]:
        H=nx.Graph();H.add_nodes_from(range(2*t+1))
        for j in range(t):H.add_edges_from(edges_of((2*j,2*j+1,2*j+2)))
        G,F,local=regular_completion(H,r); ledger=block_ledger(G)
        assert sum(map(len,F))==r*(2*t+1)+t
        assert ledger['blocks']==3*t+1 and ledger['holes']==3*r*t
        chains.append(dict(r=r,t=t,**ledger,cycles=sum(map(len,F))))
    report['triangle_chains']=chains
    # Non-cactus cores: check the general completion formula too.
    cores=[nx.complete_graph(5),nx.complete_bipartite_graph(4,4),nx.octahedral_graph()]
    for H in cores:
        H=nx.convert_node_labels_to_integers(H);r=max(dict(H.degree).values())//2+2
        G,F,local=regular_completion(H,r);block_ledger(G)
    report['other_even_cores']=len(cores)
    cases=[]
    # Regular 2-edge sums, plus the explicit forced core, exercise parity repairs.
    for r in [2,3,4,6,8]:
        for t in [2,3]:
            G=nx.disjoint_union_all([nx.complete_graph(2*r+1) for j in range(t)])
            for j in range(1,t):
                u,v=next(iter(G.subgraph(range(j*(2*r+1))).edges))
                a,b=j*(2*r+1),j*(2*r+1)+1
                G.remove_edges_from([(u,v),(a,b)]);G.add_edges_from([(u,a),(v,b)])
            leaves,tree,stat=separator_decomposition(G)
            q,ql=glue_leaf_cycles(G,leaves,tree)
            assert q==ql-stat['parity_splits'];stat.update(cycles=q,leaf_cycles=ql);cases.append(stat)
        G,F,local=regular_completion(nx.cycle_graph(3),r)
        leaves,tree,stat=separator_decomposition(G);q,ql=glue_leaf_cycles(G,leaves,tree)
        assert q==ql-stat['parity_splits'];stat.update(cycles=q,leaf_cycles=ql);cases.append(stat)
    for d,n,seed in [(4,20,1),(6,24,2),(8,30,3),(10,35,4)]:
        G=nx.random_regular_graph(d,n,seed=seed)
        leaves,tree,stat=separator_decomposition(G);q,ql=glue_leaf_cycles(G,leaves,tree)
        stat.update(cycles=q,leaf_cycles=ql);cases.append(stat)
    report['separator_checks']=cases
    peeling_checks=0
    for D in [4,6,8,12,20]:
        for seed in range(12):
            H=nx.random_regular_graph(D,D+7,seed=seed)
            rng=random.Random(seed)
            H.remove_edges_from([e for e in H.edges if rng.random()<(seed+1)/13])
            check_deficit_peeling(H,D);peeling_checks+=1
    report['deficit_peeling_checks']=peeling_checks

    report['profile_example']=profile_example()
    report['hole_Hall_checks']=hole_hall_checks()
    report['cayley_factorization']=cayley_factorization_check()
    # Verify the elementary envelope inequalities over a wide finite grid.
    envelope_checks=0
    for d in range(2,201,2):
        for b in range(3,2*d+10):
            E2=min(b*(b-1),d*b)
            assert E2<=(d+3)*(b-1)-2*d
            assert E2<=(d+3)*(b-2)-(d-3)
            envelope_checks+=1
    report['envelope_checks']=envelope_checks
    check_spec()
    out=Path('/tmp/ResearchFactorsCheck.json');out.write_text(json.dumps(report,indent=2))
    print('All targeted checks passed.')
    print('Triangle regular completions:',len(completions))
    print('Windmill completions:',len(windmills))
    print('Triangle chains:',len(chains),'other even cores:',len(cores))
    print('Separator/virtual-edge gluing checks:',len(cases))
    print('Envelope parameter checks:',envelope_checks)
    print('Deficit-paid peeling checks:',peeling_checks)
    print('Color-profile obstruction and Hamilton repair:',report['profile_example'])
    print('Hole Hall certificates:',report['hole_Hall_checks'])
    print('Cayley factorization:',report['cayley_factorization'])
    print('Results:',out)

if __name__=='__main__':main()
