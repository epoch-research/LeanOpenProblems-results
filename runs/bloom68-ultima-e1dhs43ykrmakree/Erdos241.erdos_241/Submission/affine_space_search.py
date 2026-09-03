from itertools import combinations,combinations_with_replacement

def affine_B3_search(n,k,poly):
 Q=1<<n;M=Q-1;logs=[-1]*Q;x=1
 for e in range(M):
  assert x and logs[x]<0
  logs[x]=e;x<<=1
  if x&Q:x^=poly
 assert x==1
 tested=0;good=[]
 for piv in combinations(range(n),k):
  cells=[(i,j) for i in range(k) for j in range(piv[i]+1,n) if j not in piv]
  base=[1<<p for p in piv]
  for bits in range(1<<len(cells)):
   rows=base.copy()
   for b,(i,j) in enumerate(cells):
    if bits>>b&1:rows[i]|=1<<j
   U=[0]
   for r in rows:U += [v^r for v in U]
   if 1 in U:continue
   tested+=1;A=sorted(1^u for u in U);la=[logs[z] for z in A];seen=set()
   for i,j,h in combinations_with_replacement(range(len(A)),3):
    value=(la[i]+la[j]+la[h])%M
    if value in seen:break
    seen.add(value)
   else:good.append(A)
 return tested,good
if __name__=='__main__':
 for n,k,p in [(5,2,0x25),(8,3,0x11D)]:
  tested,good=affine_B3_search(n,k,p)
  print(n,k,tested,len(good),good[:10],flush=True)
