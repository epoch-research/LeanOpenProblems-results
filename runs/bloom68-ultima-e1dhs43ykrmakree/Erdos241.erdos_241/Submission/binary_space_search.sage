from itertools import combinations_with_replacement
for n in [6,7,8,9,10,11]:
 E=GF(2^n,'t'); z=E.multiplicative_generator(); logs={}; x=E.one()
 for i in range(2^n-1): logs[x.integer_representation()]=i; x*=z
 m=2^n-1
 pairs=set(); good=[]; first=None
 for a in range(2,2^n,2):
  for b in range(a+2,2^n,2):
   if b<= (a^^b):
    V=tuple(sorted((1,a,a^^1,b,b^^1,a^^b,a^^b^^1)))
    if V in pairs: continue
    pairs.add(V)
    ls=[logs[x] for x in V]; sums=set(); okay=True
    for i,j,k in combinations_with_replacement(range(7),3):
     s=(ls[i]+ls[j]+ls[k])%m
     if s in sums:okay=False;break
     sums.add(s)
    if okay: good.append(V)
 print(n,'dim3subspaces',len(pairs),'B3',len(good),'first',good[:3],flush=True)
 if good:
  import json
  with open('/workspace/leanproject/Submission/binary_spaces_'+str(n)+'.json','w') as out: json.dump({'degree':int(n),'logs':{int(x):int(y) for x,y in logs.items()},'spaces':[[int(x) for x in v] for v in good]},out)
