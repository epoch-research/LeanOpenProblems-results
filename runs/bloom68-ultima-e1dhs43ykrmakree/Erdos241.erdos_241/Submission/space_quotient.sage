from itertools import combinations_with_replacement,product
for q,k in [(5,2),(7,2),(5,4),(7,4),(5,5),(7,5),(11,2),(11,4)]:
 E=GF(q^(3*k),'t'); z=E.multiplicative_generator(); th=z^((q^(3*k)-1)//(q^3-1)); u0=z^((q^(3*k)-1)//(q^k-1))
 # all projective K representatives, first nonzero coordinate1
 us=[]
 for i in range(k):
  for tail in product(range(q),repeat=k-i-1):
   us.append(u0^i+sum(E(a)*u0^(i+1+j) for j,a in enumerate(tail)))
 ps=[(u+th*u^q)^(q^3-1) for u in us]
 if len(set(ps))<len(ps):
  print(q,k,'projectionnotinjective',len(ps),len(set(ps))); continue
 seen={}; collision=None
 for I in combinations_with_replacement(range(len(ps)),3):
  x=ps[I[0]]*ps[I[1]]*ps[I[2]]
  if x in seen:
   collision=(I,seen[x]);break
  seen[x]=I
 print(q,k,'size',len(ps),'tripleschecked',len(seen),'collision',collision,flush=True)
