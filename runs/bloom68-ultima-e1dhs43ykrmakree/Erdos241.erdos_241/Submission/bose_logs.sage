import json
qs=[5,7,11,13,17,19,23,29,31,37,41,47,59,71,101,127]
result={}
for q in qs:
 K=GF(q^3,'t');th=K.gen();z=K.multiplicative_generator();M=q^3-1
 a=[int((th-K(i)).log(z)) for i in range(q)]
 result[int(q)]=a
 print(q,'generated',flush=True)
with open('/workspace/leanproject/Submission/bose_logs.json','w') as f:json.dump(result,f)
