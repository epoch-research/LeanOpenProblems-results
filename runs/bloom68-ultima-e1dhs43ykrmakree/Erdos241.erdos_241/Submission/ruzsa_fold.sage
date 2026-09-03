from itertools import combinations_with_replacement
for q in [3,5,7,11,13,17,19,23,29,31]:
 K=GF(q**2,'t'); theta=K.gen()
 points=[theta+K(a) for a in range(q)]
 seen={}; first=None; edges=set()
 for I in combinations_with_replacement(range(q),3):
  x=prod(points[i] for i in I); s=sum(I)%q
  if (s,-x) in seen:
   J=seen[s,-x]
   edges.add(tuple(sorted(set(I+J))))
   if first is None: first=I,J
  seen[s,x]=I
 print(q,theta.minpoly(),'fold edges',len(edges),'first',first, flush=True)
