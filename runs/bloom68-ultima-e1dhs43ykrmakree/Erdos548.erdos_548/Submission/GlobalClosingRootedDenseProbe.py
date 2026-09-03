import sys,itertools as it,json,time,subprocess
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent))
from GlobalClosingIndependentChecks import *
def rooted_iso(G,x,y):
 if G.degree(x)!=G.degree(y):return False
 A=G.copy();B=G.copy()
 nx.set_node_attributes(A,{v:int(v==x) for v in A},'mark')
 nx.set_node_attributes(B,{v:int(v==y) for v in B},'mark')
 return nx.is_isomorphic(A,B,node_match=lambda a,b:a['mark']==b['mark'])
start=time.monotonic(); checks=0
for n in range(4,10):
 Ts=[canon(T) for T in nx.nonisomorphic_trees(n)]
 cp=subprocess.Popen(['nauty-geng','-q',str(n),'0:'+str(n-3)],stdout=subprocess.PIPE)
 nh=0
 for ln in cp.stdout:
  H=canon(nx.from_graph6_bytes(ln.strip()));d=H.number_of_edges();G=nx.complement(H);nh+=1
  reps=[]
  for x in G:
   if any(rooted_iso(G,x,y) for y in reps):continue
   reps.append(x)
  for T in Ts:
   D=max(dict(T.degree()).values())
   if d+D>n-1:continue
   t_reps=[]
   for p in T:
    if any(rooted_iso(T,p,q) for q in t_reps):continue
    t_reps.append(p)
   for p,x in it.product(t_reps,reps):
    checks+=1
    if embedding(G,T,prescribed={p:x}) is None:
     out=dict(n=n,d=d,D=D,H=list(H.edges()),T=list(T.edges()),p=p,x=x)
     print('COUNTEREXAMPLE',out,flush=True)
     json.dump(out,open('/tmp/es_rooted_dense_counter.json','w'));sys.exit()
 cp.wait()
 print('done',n,'H',nh,'tests',checks,'time',time.monotonic()-start,flush=True)
