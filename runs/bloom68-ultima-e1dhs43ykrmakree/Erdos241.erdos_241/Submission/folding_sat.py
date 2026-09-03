import json,itertools,subprocess,collections,time,pathlib,sys,math
ROOT=pathlib.Path(__file__).resolve().parent
CAD='/root/.elan/toolchains/leanprover--lean4---v4.27.0/bin/cadical'
DATA=json.load(open(ROOT/'bose_logs.json'))
def setup(q,u=1,anchor=0):
 M=q**3-1;m=M//2;A=DATA[str(q)];A=[(u*(x-A[anchor]))%M for x in A]
 r=[x%m for x in A];bs=[x//m for x in A]
 seen={};edges=[]
 for I in itertools.combinations_with_replacement(range(q),3):
  s=sum(r[i] for i in I);z=s%m
  if z in seen:
   J,ss=seen[z];v=collections.Counter(I);v.subtract(J);assert all(v[i] for i in v)
   edge=(tuple(v),tuple(v.values()),(s-ss)//m)
   assert edge[2]+sum(a*bs[i] for i,a in zip(*edge[:2])) != 0
   edges.append(edge)
  else:seen[z]=(I,s)
 clauses=[]
 for ids,vs,k in edges:
  for mask in range(1<<len(ids)):
   if k+sum(a*((mask>>j)&1) for j,a in enumerate(vs))==0:
    clauses.append(tuple(-(i+1) if ((mask>>j)&1) else i+1 for j,i in enumerate(ids)))
 clauses.append((-(anchor+1),))
 return M,m,r,bs,clauses,edges

def solve(q,clauses,timeout=30):
 cnf=f'p cnf {q} {len(clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in clauses)
 try:p=subprocess.run([CAD,'--quiet'],input=cnf,text=True,capture_output=True,timeout=timeout)
 except subprocess.TimeoutExpired:return 'TIMEOUT'
 if p.returncode==20:return None
 if p.returncode!=10:raise RuntimeError((p.returncode,p.stdout,p.stderr))
 ls=[int(x) for line in p.stdout.splitlines() if line.startswith('v ') for x in line[2:].split() if x!='0']
 b=[None]*q
 for x in ls:b[abs(x)-1]=int(x>0)
 assert None not in b
 assert all(any(b[abs(x)-1]==int(x>0) for x in c) for c in clauses)
 return b

def certify(r,m,b):
 A=[r0+m*x for r0,x in zip(r,b)]
 sums=[sum(t) for t in itertools.combinations_with_replacement(A,3)]
 assert len(sums)==len(set(sums))
 return max(A)-min(A),A
if __name__=='__main__':
 qs=[int(x) for x in sys.argv[1:]] or [5,7,11,13,17,19,23,29,31,37,41,47,59,71,101,127]
 for q in qs:
  t=time.time();M,m,r,base,cls,edges=setup(q)
  count=0;best=M;bestA=None;bestb=None;done=False
  while count<32:
   b=solve(q,cls,20)
   if b is None:done=True;break
   if b=='TIMEOUT':break
   span,A=certify(r,m,b);count+=1
   if span<best:best,bestA,bestb=span,A,b
   cls.append(tuple(-(i+1) if x else i+1 for i,x in enumerate(b)))
  print(q,'edges',len(edges),'sols',count,('ALL' if done else 'MORE/timeout'),'bestspan',best,'ratio',round(best/M,6),'time',round(time.time()-t,3),flush=True)
  with open(ROOT/f'folding_result_{q}.json','w') as f:json.dump({'q':q,'M':M,'best':best,'A':bestA,'bits':bestb,'num_solutions':count,'complete':done},f)
