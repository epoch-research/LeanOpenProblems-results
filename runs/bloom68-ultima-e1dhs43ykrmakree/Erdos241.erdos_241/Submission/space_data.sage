import json
for q,n in [(2,11),(4,7)]:
 E=GF(q^n,'t'); z=E.multiplicative_generator(); x=E.one(); M=(q^n-1)//(q-1)
 logs=[-1]*(q^n)
 for j in range(q^n-1): logs[int(x.integer_representation())]=int(j%M);x*=z
 if q==2: cs=[E.zero(),E.one()]
 else:
  om=z^((q^n-1)//3);cs=[E.zero(),E.one(),om,om+1]
 basis=[[int((c*E.gen()^i).integer_representation()) for c in cs] for i in range(n)]
 times=[[int((c*E.fetch_int(i)).integer_representation()) for i in range(q^n)] for c in cs]
 with open('/workspace/leanproject/Submission/space_data_%d_%d.json'%(q,n),'w') as f:json.dump({'q':int(q),'n':int(n),'logs':logs,'basis':basis,'times':times},f,default=int)
 print('wrote',q,n,flush=True)
