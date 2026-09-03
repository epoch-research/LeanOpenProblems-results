from itertools import combinations_with_replacement
for q in [5,7,11,13,17,19,23,25,27,29,31]:
 F=GF(q,'v'); K=GF(q^3,'t'); emb=F.hom([K.multiplicative_generator()^((q^3-1)//(q-1))]) if not F.is_prime_field() else K.coerce_map_from(F)
 th=K.gen(); pts=[th-emb(a) for a in F]
 seen={}; edges=set(); first=None
 for I in combinations_with_replacement(range(q),3):
  x=prod(pts[i] for i in I)
  if -x in seen:
   J=seen[-x]; edges.add(tuple(sorted(set(I+J))))
   if first is None: first=(I,J)
  seen[x]=I
 print('Bose quotient',q,'edges',len(edges),'first',first)
